# An integral boundary direction for a finite weight set

The internal predicate `IsIntegralBoundaryCombination s f g n m` says that
`n > 0`, that `n*f + m*g` is nonnegative wherever `f` is nonnegative on
`s`, and that this combination vanishes at an element of `s` where `f`
is nonzero. The predicate itself places no finiteness condition on `s`.

The accompanying theorem `exists_integral_boundary_combination` concerns
a finite set `s` and two integer-valued functions `f` and `g`.
Suppose `g` vanishes wherever `f`
does and is nonzero somewhere on `s`. Then there are integers `n > 0`
and `m` such that `n*f + m*g` is nonnegative wherever `f` is
nonnegative, and vanishes at an element where `f` is nonzero.

The proof chooses an element `b` maximizing the rational number
`|g(b)/f(b)|`. The maximum is positive. Its defining bound gives
`|g(x)| |f(b)| ≤ |g(b)| |f(x)|` at every element of `s`.
If `g(b)` is positive, use `(n,m) = (g(b), -f(b))`; otherwise use
`(-g(b), f(b))`. The absolute-value bound proves nonnegativity,
and the value at `b` is zero by cancellation.

The construction is intended for actual integral Lie weights of
cocharacters. It assumes neither negation stability nor a root system.
It makes no assertion about existence or classification of parabolics.
It is an internal finite-set argument using Mathlib's finite maximum,
ordered rational arithmetic, and integer arithmetic; no external
literature assertion is used.
