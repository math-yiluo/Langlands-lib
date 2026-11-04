# Polynomials that are additive on every algebra are `p`-polynomials

Let `A` be a commutative ring in which a prime `p` vanishes. A polynomial over `A`
is *additive on every algebra* if `Q(x + y) = Q(x) + Q(y)` for all `x, y` in every
commutative `A`-algebra `B` (in the universe of `A`). This module proves that such
a polynomial in finitely many variables is a finite sum of terms
`c · X j ^ p ^ s`. Everything is in namespace
`Langlands.GroupScheme.RelativeRoot.AdditiveSupport`.

## One variable

- `choose_mul_coeff_eq_zero`: let `q` be additive on every algebra and
  `0 < i < m`. Then `(m choose i) · q_m = 0`. Evaluate the additivity identity at
  the two variables `X` and `Y` of `A[X][Y]`. The left side `q(X + Y)` is the
  Taylor expansion of `q`. Its coefficient of `Y^i X^(m-i)` is the coefficient
  `(m choose i) · q_m` of the `i`-th Hasse derivative. On the right side
  `q(X) + q(Y)` that coefficient is zero, since `i ≠ 0` and `m - i ≠ 0`.
- `coeff_eq_zero_of_additive`: if `(p : A) = 0` and `m` is not a power of `p`,
  then `q_m = 0`. For `m = 0`, additivity at `0 + 0` gives `q(0) = 0`. For
  `m > 0`, Lucas' theorem in the form
  `Choose.eq_pow_multiplicity_of_choose_modEq_zero_nat` says the following: if
  every `m choose i` with `1 ≤ i ≤ m - 1` were divisible by `p`, then `m` would
  be a power of `p`. So some `m choose i` is prime to `p`. A Bézout identity
  `(m choose i) · a + p · b = 1` holds in `ℤ`; its image in `A` makes
  `m choose i` a unit in `A`, because `p = 0` there. Hence `q_m = 0` by the
  previous lemma.
- `eq_sum_pow_of_additive`: if `deg q < N`, then
  `q = ∑_{s < N} q_{p^s} · X ^ p ^ s`. Compare coefficients. The sum is
  harmless because `p ^ s ≥ s + 1 > deg q` for `s ≥ N`.

## Several variables

`MvPolynomial.exists_eq_sum_pow_of_additive`: let the variables `σ` form a
finite type, let `(p : A) = 0`, and let `Q : MvPolynomial σ A` be additive on
every algebra. Then there are `N₀` and coefficients `c j s` such that for every
`N ≥ N₀`

`Q = ∑ j, ∑ s < N, C (c j s) * X j ^ p ^ s`.

The proof works one variable at a time.

1. Additivity, iterated over a finite sum, gives
   `Q = ∑ j Q(Pi.single j (X j))`. Each summand is `q_j(X j)`, where
   `q_j = Q(Pi.single j X)` is a one-variable polynomial.
2. Each `q_j` is additive on every algebra, because evaluation commutes with the
   substitution.
3. The one-variable result applies to each `q_j` with a common bound `N₀`
   exceeding every degree.

The index type is `σ : Type`, so that `MvPolynomial σ A` lives in the universe of
`A` and can be used as a test algebra.

## Provenance

This is the "only if" direction of Conrad–Gabber–Prasad, *Pseudo-reductive
Groups*, 2nd ed., Proposition B.1.3 (p. 562). That proposition says a polynomial
over a field of characteristic `p` is a `p`-polynomial (Definition B.1.2) if and
only if the map `Ga^n → Ga` it defines is a homomorphism. The book leaves the
proof to the reader; the Lucas and Bézout argument above is the one implemented
here. The statement here is more general: `A` is any commutative ring in which
`p = 0`, and homomorphy of the map of schemes is expressed as additivity on every
commutative `A`-algebra. It is used in the proof of
`TorusVectorActionLinearizationStatement`.
