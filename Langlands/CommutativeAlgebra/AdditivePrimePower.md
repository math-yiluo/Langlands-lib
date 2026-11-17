# Additive prime-power maps and the characteristic

This internal derived unit records an elementary fact used for Conrad,
*Reductive group schemes* (2014), Proposition 6.1.7. In that proof the
characteristic exponent `p` of the root-datum isogeny vanishes on the base
wherever some root factor `p ^ n` differs from `1`. On a root group the
homomorphism has the form `x ↦ c x ^ (p ^ n)` with `c` a unit, and additivity of
this map forces `p = 0`. The statements here are the purely ring-theoretic part
of that argument. All rings are arbitrary commutative rings.

`natCast_prime_eq_zero_of_choose` assumes that `p` is prime, `n ≠ 0`, and that
the binomial coefficients `C(p ^ n, k)` vanish in `A` for all `0 < k < p ^ n`.
It concludes `(p : A) = 0`. The proof uses two of these coefficients. The
coefficient `C(p ^ n, 1) = p ^ n` vanishes. The coefficient
`N = C(p ^ n, p ^ (n - 1))` has `p`-adic valuation exactly `1`, by
`Nat.factorization_choose_prime_pow`, so `N = p * m` with `m` prime to `p`. Then
`m` and `p ^ (n - 1)` are coprime, so `a m + b p ^ (n - 1) = 1` for some integers
`a` and `b`. Multiplying by `p` gives `p = a N + b p ^ n`, and both terms vanish
in `A`.

`mul_choose_eq_zero_of_add_pow` takes `c : B₀` and `q : ℕ` with the identity
`c (X + Y) ^ q = c X ^ q + c Y ^ q` in the two-variable polynomial ring
`B₀[X][X]`. Here `Y` is the inner variable `C X`. It concludes `c * C(q, k) = 0`
for all `0 < k < q`. The proof compares the coefficient of `X ^ k Y ^ (q - k)` on
both sides.

`natCast_prime_eq_zero_of_add_pow` combines the two results. If `c` is a unit,
`p` is prime, `n ≠ 0`, and the map `x ↦ c x ^ (p ^ n)` is additive on the two
variables of `B₀[X][X]`, then `(p : B₀) = 0`. Cancelling the unit `c` reduces this
to the binomial vanishing of the first lemma.
