# Euler polynomials determined by squared Euler characteristics

This internal module reads off the top coefficient of the actual line-bundle Euler
polynomial `lineBundleEulerPolynomial f L g` from squared Euler characteristics.
It is meant for an abelian variety, where Milne, Theorem 13.3 (a) gives
`χ(L^k)^2 = deg φ_(L^k) = k^(2g) deg φ_L`. The module does not prove that formula.
It takes the squared values as a hypothesis.

## Polynomial lemma

`polynomial_eq_C_mul_X_pow_of_sq_eval` takes a rational polynomial `P`, a natural
number `g` and a rational `c ≥ 0`. Suppose that `P(k)^2 = c^2 k^(2g)` for every
positive integer `k` and that `P(1) ≥ 0`. Then `P = c X^g`.

Proof as implemented: the polynomial `P^2 - (c X^g)^2` vanishes at every positive
integer. That set is infinite, since `k ↦ k + 1` is injective from `ℕ` to `ℚ`.
So `P^2 - (c X^g)^2` is zero by `Polynomial.eq_zero_of_infinite_isRoot`.
`sq_eq_sq_iff_eq_or_eq_neg` then gives `P = c X^g` or `P = -c X^g`. In the second
case `P(1) = -c`, and with `P(1) ≥ 0` and `c ≥ 0` this forces `c = 0`, so again
`P = c X^g`.

## Euler-coefficient corollary

`lineBundleEulerPolynomial_coeff_eq_of_eulerCharacteristic_sq` works with a proper
morphism `f : X ⟶ Spec K` over a field, where `X` is Noetherian and separated and
`topologicalKrullDim X ≤ g`. Let `L` be a line bundle on `X` and `c` a natural
number. Assume:

- `hsq`: for every positive `k`, the actual Euler characteristic of
  `tensorPow L.obj k` satisfies `χ(L^k)^2 = c^2 k^(2g)` in `ℤ`, for every
  finite-cohomology witness;
- `hpos`: `χ(L^1) ≥ 0`.

Then the degree-`g` coefficient of `lineBundleEulerPolynomial f L g` equals `c`.

Proof as implemented: the published `lineBundleEulerPolynomial_eval` identifies the
polynomial's value at each natural `k` with `χ(L^k)`. The witness comes from
`lineBundleTensorPow_hasFiniteCohomology`. Casting the two hypotheses to `ℚ` gives the
inputs of the polynomial lemma with `P` the Euler polynomial. That lemma gives
`P = c X^g`, whose `g`-th coefficient is `c`.

The hypotheses refer only to positive powers. The exponent-zero value `χ(𝒪_X)` is
not used.

## Provenance

The module is internal. It combines the Library's actual Euler polynomial and its
evaluation theorem with Mathlib's root-counting for polynomials. Its intended input
is the Euler-square formula `χ(L)^2 = deg φ_L` (Milne, *Abelian Varieties*,
Theorem 13.3 (a); GIT, Proposition 6.13 (iii)), applied to the powers of an ample
line bundle together with `deg φ_(L^k) = k^(2g) deg φ_L`. Neither of these is
proved here.
