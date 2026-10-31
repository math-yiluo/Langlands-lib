# Finite sums of products of continuations and functional equations

Module `Langlands.Representation.GodementJacquet.FunctionalEquationProducts`.

This module is the one-variable algebra of the functional-equation comparison
in Godement–Jacquet, *Zeta Functions of Simple Algebras* (1972), Theorem 3.4,
printed 39–42. There, a zeta integral of a parabolically induced representation is
written as a finite sum of products of zeta integrals of the two blocks, and the same
finite sum, with Fourier-transformed tests and transformed coefficients, gives the
dual integral. The block functional equations then give the functional equation
of the induced integral, with product L-polynomials and the product epsilon factor.
This module proves only that last algebraic step, in the spectral variable
`X = q^(-s)`. It contains no analytic or representation-theoretic content. The
expansion of the integrals into finite sums of products is a separate input
(the hypotheses `hZ` and `hZD` below).

All statements use the Library's predicates from
`Langlands.Representation.RankinSelberg.RationalContinuation` and
`Langlands.Representation.RankinSelberg.FunctionalEquationStatement`:

- `HasRationalContinuation q f R`: there is a real `a` such that for every `s`
  with `a < Re s`, the denominator of `R` does not vanish at `q^(-s)` and
  `f s = R(q^(-s))`.
- `NormalizedFunctionalEquation q P Pd 1 c 0 m R RD`: for every `s` at which the
  denominators of `R` at `q^(-s)` and of `RD` at `q^(-(1-s))` are both nonzero,
  `Pd(q^(-(1-s))) · RD(q^(-(1-s))) = 1^0 · c · (q^(-s))^m · P(q^(-s)) · R(q^(-s))`.
  The central scalar is `1` and the sign exponent is `0`, the case used by the
  target package.

## Evaluation lemmas

- `ratFunc_denom_mul_eval_ne_zero`, `ratFunc_denom_add_eval_ne_zero`: at a point
  where the denominators of `A` and `B` do not vanish, neither does the denominator
  of `A * B` or of `A + B`. The proof uses `RatFunc.denom_mul_dvd` and
  `RatFunc.denom_add_dvd`. The Library has equivalent private lemmas, which other
  modules cannot use.
- `ratFunc_sum_mul_eval`: at such a point, for every summand, the finite sum
  `∑ j ∈ J, A j * B j` has nonzero denominator and evaluates termwise. The proof is
  by induction on `J`, using `RatFunc.eval_add` and `RatFunc.eval_mul`.
- `ratFunc_eval_continuousAt`: the evaluation `y ↦ R(y)` is continuous at every
  point where the denominator of `R` does not vanish, because there it equals
  `num(y)/denom(y)`.

## Continuation lemma

- `hasRationalContinuation_sum_mul`: if `f j` has continuation `A j` and `g j` has
  continuation `B j` for every `j ∈ J`, then `s ↦ ∑ j ∈ J, f j s * g j s` has
  continuation `∑ j ∈ J, A j * B j`. It combines the Library lemmas
  `HasRationalContinuation.mul` (from `LaurentTransport`) and
  `RationalContinuationLinear.continuation_sum`.

## Spectral point lemmas

- `spectralPoint_add`: `q^(-(a+b)) = q^(-a) · q^(-b)` for `q > 0`.
- The imported `Langlands.RankinSelberg.spectralPoint_ne_zero_of_pos`
  from `RationalContinuation` gives `q^(-s) ≠ 0` for `q > 0`.
- `continuous_spectralPoint`: `s ↦ q^(-s)` is continuous for `q > 0`.
- `finite_ray_zeros`: for `q > 1`, a nonzero polynomial `D`, a base point `s₀` and
  a nonzero real `ε`, only finitely many real `t` satisfy
  `D(q^(-(s₀ + ε t))) = 0`. The map `t ↦ q^(-(s₀ + ε t))` is injective
  (by `spectralPoint_add` and `spectralPoint_ofReal_injective`) and `D` has finitely
  many roots.

## The functional-equation algebra

`normalizedFunctionalEquation_sum_mul`: let `q > 1` and `J` a finite index set.
Suppose that for every `j ∈ J`

- `NormalizedFunctionalEquation q P₀ Pd₀ 1 c₀ 0 m₀ (R₀ j) (RD₀ j)`, and
- `NormalizedFunctionalEquation q P₁ Pd₁ 1 c₁ 0 m₁ (R₁ j) (RD₁ j)`.

Then

`NormalizedFunctionalEquation q (P₀ * P₁) (Pd₀ * Pd₁) 1 (c₀ * c₁) 0 (m₀ + m₁)
(∑ j ∈ J, R₀ j * R₁ j) (∑ j ∈ J, RD₀ j * RD₁ j)`.

The polynomials, units and exponents are the same for every `j`. Only the rational
functions depend on `j`.

Proof. Fix `s₀` at which the denominators of the two sums (at `q^(-s₀)` and
`q^(-(1-s₀))`) do not vanish. A summand denominator may still vanish at `s₀`,
because the sum can cancel a pole of a summand. So the equation is not proved at
`s₀` directly. Write `L(s)` and `Rt(s)` for the two sides of the claimed equation.
Both are continuous at `s₀`, by `ratFunc_eval_continuousAt` and the continuity of
the spectral point and of polynomial evaluation. Along the real ray `s₀ + t`, only
finitely many `t` make some summand denominator vanish at `q^(-(s₀+t))` or at
`q^(-(1-(s₀+t)))` (`finite_ray_zeros` with `ε = 1` and `ε = -1`). For all other
`t`, both sums evaluate termwise (`ratFunc_sum_mul_eval`). Multiplying the two
block equations term by term gives
`(Pd₀ Pd₁)(Y) · RD₀ j(Y) · RD₁ j(Y) = (c₀ c₁) X^(m₀+m₁) · (P₀ P₁)(X) · R₀ j(X) · R₁ j(X)`
with `X = q^(-s)`, `Y = q^(-(1-s))`, using `zpow_add₀` (as `X ≠ 0`). Summing over
`j` gives `L(s₀+t) = Rt(s₀+t)` for all `t` outside a finite set, hence eventually
along the punctured neighbourhood filter of `0` in `ℝ` (`nhdsNE_le_cofinite`). Both
sides tend to their values at `s₀`, so `L(s₀) = Rt(s₀)` by uniqueness of limits
(`tendsto_nhds_unique_of_eventuallyEq`).

`normalizedFunctionalEquation_of_eventually_sum_mul` is the form used for
assembly. Let `q > 1`. Suppose `Z` has continuation `R` and `ZD` has continuation
`RD`. Suppose that on some right half-plane `Z s = ∑ j ∈ J, z₀ j s * z₁ j s` and,
on some possibly different right half-plane, `ZD s = ∑ j ∈ J, zd₀ j s * zd₁ j s`,
with the same finite `J`. Suppose further that `z₀ j, z₁ j, zd₀ j, zd₁ j` have
continuations `R₀ j, R₁ j, RD₀ j, RD₁ j`, and that the two block functional
equations above hold for every `j ∈ J`. Then
`NormalizedFunctionalEquation q (P₀ * P₁) (Pd₀ * Pd₁) 1 (c₀ * c₁) 0 (m₀ + m₁) R RD`.

Proof. By `hasRationalContinuation_sum_mul` and
`RationalContinuationLinear.continuation_of_eq_on_right`, `Z` also has continuation
`∑ R₀ j * R₁ j`. Uniqueness of rational continuation
(`HasRationalContinuation.unique`, which needs `q > 1`) gives
`R = ∑ R₀ j * R₁ j`. In the same way, `RD = ∑ RD₀ j * RD₁ j`. Then apply
`normalizedFunctionalEquation_sum_mul`.

## Scope

The module proves nothing about zeta integrals. In the intended use, `Z` and `ZD`
are the induced zeta integral and its transformed integral, and `z₀ j, z₁ j,
zd₀ j, zd₁ j` are block zeta integrals. Then `hZ` and `hZD` are the matched finite
expansions with the same index set, and the block equations come from the supplied
block packages. Each of those inputs must be proved separately.
