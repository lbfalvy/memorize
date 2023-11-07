//! Cache the return values of an effectless closure in a hashmap
//! Inspired by the `closure_cacher` crate, but attempts to provide a more
//! versatile implementation.
//!
//! ```
//! use memorize::{cached, Cache};
//!
//! let demo = cached(|arg, _| arg * 2);
//! assert_eq!(demo.find(&7), 14);
//! ```
//!
//! The second argument is a callback, it can be used for recursion.
//!
//! ```
//! use memorize::{cached, Cache};
//!
//! let demo = cached(|arg, r| match arg {
//!   1 | 2 => 1,
//!   n => r.r(&(n - 1)) + r.r(&(n - 2)),
//! });
//! assert_eq!(demo.find(&15), 610)
//! ```

use std::borrow::Borrow;
use std::cell::RefCell;
use std::hash::Hash;

use hashbrown::HashMap;

/// A cache that can be polled for a value with its borrowed form.
pub trait Cache<I, O> {
  /// Obtain the return value of the function for the owned version of this
  /// input.
  fn find<Q: ?Sized>(&self, q: &Q) -> O
  where
    Q: Eq + Hash + ToOwned<Owned = I>,
    I: Borrow<Q>;
}

/// A wrapper around the recursive self-handle to keep `rust-analyzer` from
/// hanging. See [rust-analyzer#11063](https://github.com/rust-lang/rust-analyzer/issues/11063)
#[derive(Clone, Copy)]
pub struct Recur<'a, I, O>(pub &'a dyn for<'b> Fn(&'b I) -> O);
impl<'a, I, O> Recur<'a, I, O> {
  pub fn r(&self, i: &I) -> O { self.0(i) }
}

/// Cache the return values of an effectless closure in a hashmap. This struct
/// is available for unforeseen use cases, but you should probably use [cached]
/// and [Cache]
struct CacheImpl<I, O, F> {
  store: RefCell<HashMap<I, O>>,
  closure: F,
}

impl<I: Eq + Hash + Clone, O: Clone, F: for<'a> Fn(I, Recur<'a, I, O>) -> O>
  CacheImpl<I, O, F>
{
  pub fn new(closure: F) -> Self {
    Self { store: RefCell::new(HashMap::new()), closure }
  }
}

impl<I: Eq + Hash + Clone, O: Clone, F: for<'a> Fn(I, Recur<'a, I, O>) -> O>
  Cache<I, O> for CacheImpl<I, O, F>
{
  /// Produce and cache a result by cloning I if necessary
  fn find<Q: ?Sized>(&self, q: &Q) -> O
  where
    Q: Eq + Hash + ToOwned<Owned = I>,
    I: Borrow<Q>,
  {
    let closure = &self.closure;
    if let Some(v) = self.store.borrow().get(q) {
      return v.clone();
    }
    // In the moment of invocation the refcell is on immutable
    // this is important for recursive calculations
    let result = closure(q.to_owned(), Recur(&|i: &I| self.find::<I>(i)));
    let mut store = self.store.borrow_mut();
    let (_, v) = store
      .raw_entry_mut()
      .from_key(q)
      .or_insert_with(|| (q.to_owned(), result));
    v.clone()
  }
}

impl<I, O, F> IntoIterator for CacheImpl<I, O, F> {
  type IntoIter = hashbrown::hash_map::IntoIter<I, O>;
  type Item = (I, O);
  fn into_iter(self) -> Self::IntoIter {
    let CacheImpl { store, .. } = self;
    let map = store.into_inner();
    map.into_iter()
  }
}

/// Memoize a function, returning an opaque object that remembers arguments and
/// return values.
pub fn cached<I: Eq + Hash + Clone, O: Clone>(
  func: impl for<'a> Fn(I, Recur<'a, I, O>) -> O,
) -> impl Cache<I, O> {
  CacheImpl::new(func)
}

#[cfg(test)]
mod test {
  use std::cell::RefCell;

  use super::{Cache, CacheImpl};

  #[test]
  fn works() {
    let runs = RefCell::new(0);
    let cache = CacheImpl::new(|arg, _| {
      *runs.borrow_mut() += 1;
      arg * 2
    });
    assert_eq!(*runs.borrow(), 0, "callback ran without argument??");
    cache.find(&1);
    assert_eq!(*runs.borrow(), 1, "callback ran once and was recorded");
    cache.find(&1);
    assert_eq!(*runs.borrow(), 1, "cached value reused");
    cache.find(&2);
    assert_eq!(*runs.borrow(), 2, "new value passed to callback");
    cache.find(&1);
    assert_eq!(*runs.borrow(), 2, "cache used after unrelated call");
  }

  #[test]
  fn recursive() {
    let runs = RefCell::new(0);
    let cache = CacheImpl::new(|val, r| {
      *runs.borrow_mut() += 1;
      match val {
        1 | 2 => 1,
        n => r.r(&(n - 1)) + r.r(&(n - 2)),
      }
    });
    assert_eq!(cache.find(&15), 610, "correct fibonacci number");
    assert_eq!(*runs.borrow(), 15, "evaluated for numbers 1-15 exactly once");
  }
}
