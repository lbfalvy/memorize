Cache the return values of an effectless closure in a hashmap. Inspired by the [closure_cacher](https://docs.rs/closure_cacher) crate, but attempts to provide a more versatile implementation.

```rs
use memorize::{cached, Cache};

let demo = cached(|arg, _| arg * 2);
assert_eq!(demo.find(&7), 14);
```

The second argument is a callback, it can be used for recursion.

```rs
use memorize::{cached, Cache};

let demo = cached(|arg, r| match arg {
  1 | 2 => 1,
  n => r(&(n - 1)) + r(&(n - 2)),
});
assert_eq!(demo.find(&15), 610)
```