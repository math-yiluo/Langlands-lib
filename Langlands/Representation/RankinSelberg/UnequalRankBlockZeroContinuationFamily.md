# Bilinear continuation families of the unequal-rank integrals

Authors: Worker 822 (Lean) and Worker 233 (Markdown). Part of the proof task
`4564f536-d9dc-4d9a-aeb5-4ee980417bd3` for the published statement
`Langlands.RankinSelberg.UnequalRankBlockZeroContinuedFormsStatement`; its
consumers are `UnequalRankBlockZeroCovariance` and
`UnequalRankBlockZeroContinuedFormsProof`.

This module turns the rational continuations of the actual unequal-rank
integrals into a bilinear map with values in rational functions, and turns
such a map into a complex bilinear form by evaluation at a point where every
value is regular. It works for an arbitrary block `(j, k)` with
`hr : r = n + (j + k + 1)`, over a field `F` with a topology and measurable
structure, with any measures `μ` on `LeftUnipotentQuotient n F` and `ν` on
`Matrix (Fin j) (Fin (n + 1)) F` and representations `π`, `σ` with Whittaker
functionals `ℓ`, `ℓ'` in independent universes. Its only analytic input is
the Library's `UnequalRankAnalyticAt j k hr q ψ abv μ ν π σ ℓ ℓ'` (written `hA`
below), whose components give convergence on a right half-plane (`hA.1`),
existence of a rational continuation for every pair of model vectors
(`hA.2.1`) and a normalized generator of the rational-value set
(`hA.2.2.2`). The family itself also needs `1 < q` and s-finite `μ` and `ν`.

Nothing published is redefined. The module uses `HasRationalContinuation`,
`unequalRankIntegralAt`, `unequalRankValuesAt`, `IsNormalizedGenerator`,
`RegularAt` (the reduced denominator does not vanish), `laurentToRatFunc` and
`spectralPoint` as published. Rational functions are `RatFunc ℂ`
(`RationalFunctions`), evaluated with `RatFunc.eval (RingHom.id ℂ)`.

## Evaluation at regular points

For complex modules `M`, `M'`:

- `regularAt_C`: constants are regular everywhere.
  `eval_smul_of_regularAt`: at a regular point, `eval z (c • R) = c · eval z R`.
- `regularAt_of_clears`: if `z ≠ 0`, `P.eval z ≠ 0` and
  `laurentToRatFunc a = P · R` for some Laurent coefficients `a`, then `R` is
  regular at `z`. Proof: `R = laurentToRatFunc a · P⁻¹`. The first factor is
  regular at every nonzero point (the published `laurentToRatFunc_regular`),
  and `P⁻¹` is regular where `P` does not vanish (`RegularAt.inv`).
- `eval_C_mul_X_zpow_mul`: at a nonzero point `z` where `R` is regular,
  `eval z (C c · X^m · R) = c · z^m · eval z R` for every `m : ℤ`.
- `evalForm C z hreg`: for a bilinear map
  `C : M →ₗ[ℂ] M' →ₗ[ℂ] RationalFunctions` and a point `z` at which every
  value `C f f'` is regular (`hreg`), the bilinear form
  `f, f' ↦ eval z (C f f')`. `evalForm_apply` (`rfl`, simp) gives its values.
  The bilinearity proof uses the published `eval_add` and this module's
  `eval_smul_of_regularAt`. These need regularity of the summands at `z`,
  which `hreg` gives for every value. So no rational function is ever
  evaluated at a pole.

## The continuation family

Fix `hq : 1 < q`, s-finite `μ` and `ν`, and `hA`.

- For model vectors `f`, `f'` a rational continuation of
  `unequalRankIntegralAt j k hr ψ abv μ ν f f'` is chosen with
  `Classical.choose` from `hA.2.1` (private `blockValue`). By the published
  `HasRationalContinuation.unique` (valid since `1 < q`), it equals every other
  rational continuation of the same integral (private `blockValue_eq`).
  The published `UnequalRankAnalyticAt.continuation` makes a choice of the
  same kind; by uniqueness the two agree, and this module does not use it.
- Linearity of the integrals (private lemmas, after `subst hr`). Additivity
  holds on a common right half-plane: the maximum of the two convergence
  abscissae from `hA.1`, through `unequalRankIntegral_add_left` and
  `unequalRankIntegral_add_right` of `UnequalRankBlockZeroIntegralLaws`.
  Homogeneity holds at every `s`.
- `blockContinuationFamily hq hA` is the bilinear map
  `(coefficientModel π ℓ).toSubmodule →ₗ[ℂ]
  (coefficientModel σ ℓ').toSubmodule →ₗ[ℂ] RationalFunctions` with these
  values. Each linearity law of the map is an equality of rational functions:
  the right-hand side is a rational continuation of the left-hand integral by
  the published `continuation_add`, `continuation_of_eq_on_right` and
  `hasRationalContinuation_const_mul`, and uniqueness identifies it with the
  chosen value. Linearity is thus never derived from evaluations, in
  particular not at poles.
- `blockContinuationFamily_spec`: each value is a rational continuation of its
  integral. `blockContinuationFamily_eq`: each value equals every rational
  continuation of its integral.
- `blockContinuationFamily_of_integral`: if for every complex `t`

  `I(f₂, f'₂)(t) = c · spectralPoint q t ^ m · I(f₁, f'₁)(t)`,

  then `family f₂ f'₂ = C c · X^m · family f₁ f'₁`. Proof: the published
  `HasRationalContinuation.monomial_mul` makes the right side a continuation of
  the left integral, then `blockContinuationFamily_eq`. The covariance laws of
  the Covariance module are instances of this lemma.
- `UnequalRankAnalyticAt.exists_normalizedGenerator`: a normalized generator
  `P` of `unequalRankValuesAt j k hr q ψ abv μ ν π σ ℓ ℓ'` exists (`hA.2.2.2`).
  `blockContinuationFamily_clears`: for such a `P`, every value of the family is
  cleared by `P`, that is `laurentToRatFunc a = P · family f f'` for some
  Laurent coefficients `a`. Proof: by the published
  `unequalRankValuesAt_eq_set`, the value lies in the rational-value set, and
  `IsNormalizedGenerator.clearsDenominators` applies.

Together with `regularAt_of_clears`, every value of the family is regular at
each `z ≠ 0` with `P.eval z ≠ 0`. The Proof module evaluates the family with
`evalForm` exactly at such points: `z = spectralPoint q s` for the original
family and `z = spectralPoint q (1 - s)` for the complementary one.

## Provenance

JPSS = H. Jacquet, I. I. Piatetski-Shapiro and J. A. Shalika, *Rankin-Selberg
Convolutions*, Amer. J. Math. **105** (1983), §2.11, printed pp.398–399
(one-based PDF pages 33–34 of the registered scan `jpss-1983-rankin-selberg`).
JPSS (2.11.2) and (2.11.4) are stated for the meromorphically continued
integrals, "except for finitely many `q^{-s}`". This module supplies the
device the proof uses for that phrase. The continuations are packaged as a
bilinear family of rational functions, then evaluated at a spectral point
off the zeros of a normalized generator, where every value is regular. JPSS
contains no such construction. The family, the choice through uniqueness of
continuations, and the evaluation form are internal to this proof. They
follow the pattern of the published `EqualRankContinuationFamily`, except
that values are evaluated directly rather than through Laurent lifts. The
current registration, the central library, and the project and Library note
locations were checked for errata. No registered erratum to JPSS 1983 was
found. The registered Jacquet 2012 correction concerns the 1981 conductor
paper only.
