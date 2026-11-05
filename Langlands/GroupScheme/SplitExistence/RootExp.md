# The exponential of a divided-power family

Author: Worker 1398.

`IsDividedPowerFamily e` says `e 0 = 1`, `e a * e c = C(a+c, a) • e (a+c)` and `e k = 0` for
`k > n`. Then `divExp e` is additive: `divExp_mul` proves `exp(s) exp(t) = exp(s + t)` by
expanding both sides as sums over pairs `(a, c)`, reindexing the right side over antidiagonals
(binomial theorem `add_pow`) and discarding the vanishing terms with `a + c > n`.
`divExp_zero`, `divExpUnit` (the unit with inverse `exp(-s)`), `divExpHom : Multiplicative R →*
GL_n(R)`, and `divExp_map` (compatibility with ring homomorphisms) follow. Internal lemma.
