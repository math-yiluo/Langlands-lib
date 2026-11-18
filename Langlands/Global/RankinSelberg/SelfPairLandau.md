# Landau's theorem for Whittaker–Mellin integrals with nonnegative weight

Module `Langlands.Global.RankinSelberg.SelfPairLandau`, namespace
`Langlands.Global.RankinSelbergGlobal.SelfPairLandau`.

This is an internal helper for the positivity proof of Jacquet–Shalika I, Lemma (5.2)
(Task 6821, `CuspidalSelfPairContinuationStatement`). It contains no `Prop`-valued
statement definitions. It applies Landau's theorem for two-sided Laplace transforms of
nonnegative functions (`Langlands.Analysis.LandauMellin`) to integrals over
`N_n(𝔸) \ GL_n(𝔸)` of the form

`G(s, q) = f(q) · exp (s · log |det g|)`,  `g = q.out`,  `f ≥ 0`.

For a unitary cuspidal `π`, take `W' = conj W` in the conjugate realization and a
nonnegative real Schwartz–Bruhat function `Φ`. Then the equal-rank Whittaker integrand
`W(g) W'(g) Φ(e_n g) |det g|^s` has this form, with weight `f(q) = |W(g)|² Φ(e_n g)`.

## Provenance

The idea that positivity of the Rankin–Selberg integrand for `π × π̃` controls convergence
on `Re s > 1` comes from Jacquet–Shalika, *On Euler products and the classification of
automorphic representations I*, Amer. J. Math. 103 (1981): proof of Lemma (5.2)
pp. 554–555, and the positivity argument in the proof of (4.8), p. 553. The analytic input
is Landau's theorem in the form of Widder, *The Laplace Transform* (1941), Chapter II,
Theorem 5b, and Hardy–Riesz (1915), Theorem 10, as formalized in
`Langlands.Analysis.LandauMellin`. The statements here are internal consequences of that
module. Each hypothesis is stated explicitly; nothing is assumed about unfolding or Euler
products.

## Definitions

* `logDet n q = log |det q.out|`: the Mellin phase at the representative of a class.
  `measurable_logDet` proves measurability: `|det|` is left `N_n(𝔸)`-invariant
  (`GaugeReduction.detNorm_unipotent_mul`), so `q ↦ |det q.out|` is the continuous descent
  `LeftCosetSpace.lift` of the continuous function `|det|` (`detNorm_out_eq_lift`,
  `continuous_detNorm_out`).
* `IsMellin G f`: for all `s` and `q`,
  `G s q = f q * exp (s * log |det q.out|)`. This is the shape of
  `SelfPair.equalWhittakerIntegrand_conjugate` in the self-pair helper module.

## Main results

Throughout, `f ≥ 0` pointwise and `ν` is any measure on `N_n(𝔸) \ GL_n(𝔸)`.

* `IsMellin.aestronglyMeasurable_weight`: if `G σ` is almost everywhere strongly
  measurable at one real `σ`, so is `f`.
* `IsMellin.integrable_real`, `IsMellin.integrable_of_real`: integrability of `G σ` at a
  real point is integrability of `f e^{σ logDet}`. Integrability of `G s` at a complex
  point follows from the real integrability at `Re s`.
* **`IsMellin.integrable_of_differentiableOn`** (Landau): suppose `G s` is integrable for
  `σ₁ < Re s` and `∫ G s dν = I s` there, with `I` holomorphic on `σ₀ < Re s`. Then `G s`
  is integrable for every `s` with `σ₀ < Re s`.
  `IsMellin.integrable_real_of_differentiableOn` is the real version.
* `IsMellin.differentiableOn_setIntegral`: if `G s` is integrable for `σ₀ < Re s`, then
  for every set `A` the partial integral `s ↦ ∫_A G s dν` is holomorphic on `σ₀ < Re s`.
  `IsMellin.differentiableOn_integral` is the case `A = univ`.
* Real points:
  * `IsMellin.setIntegral_real`: `∫_A G σ dν` is the real number
    `∫_A f e^{σ logDet} dν` (coerced to `ℂ`).
  * `setIntegral_real_nonneg`: this real number is nonnegative.
  * `setIntegral_real_mono`: if `A ⊆ B` and the real integrand is integrable, then the
    integral over `A` is at most the integral over `B`.
  * `setIntegral_real_pos_iff`: the real integral is positive iff `ν(A ∩ support f) > 0`.
  * `setIntegral_real_pos_iff_pos`: positivity therefore does not depend on the real
    point.
* **`integrable_and_differentiableOn_partial`**: the case of the equal-rank Whittaker
  integrand `equalWhittakerIntegrand F W W' Φ` with `ν = whittakerQuotientMeasure`.
  Suppose it has Mellin form with nonnegative weight, is integrable for `σ₁ < Re s`, and
  `equalWhittakerIntegral` agrees there with some `I` holomorphic on `σ₀ < Re s`. Then on
  `σ₀ < Re s`:
  * the integrand is integrable;
  * `equalWhittakerIntegral F W W' Φ` is holomorphic;
  * every partial integral `partialEqualWhittakerIntegral F S W W' Φ` is holomorphic.

  In the application, `σ₀ = 1`. The continuation `I` comes from
  `EqualAnalytic.equalAnalyticStatement_proof`: for `η = ω ω̄ = 1` the pole set is
  `{0, 1}`. The half-plane of agreement comes from `EqualUnfoldingStatement`.
* `partialEqualWhittakerIntegral_real`: for the same integrand in Mellin form, at a real
  point `σ` the partial integral `partialEqualWhittakerIntegral F S W W' Φ σ` equals the
  real number `∫_(unipotentIntegralClasses F (r+1) S) f e^{σ logDet} dν` (coerced to `ℂ`).
  The two sets of integration agree by definition.
* `setIntegral_real_pos_of_re_pos`: if, in addition, `f ≥ 0`, the integrand is integrable
  at real points `σ₀` and `σ`, and `Re (partialEqualWhittakerIntegral F S W W' Φ σ₀) > 0`,
  then the real integral `∫_(unipotentIntegralClasses F (r+1) S) f e^{σ logDet} dν` is
  positive. The proof combines the previous item with `setIntegral_real_pos_iff_pos`.

## Proof outline

Put `u = logDet (r + 1)`. `IsMellin` identifies `G s` with the integrand
`(f q : ℂ) * exp (s * u q)` of `LandauMellin.bilateral ν f u s`. Measurability of `f` comes
from measurability of `G` at one real point: `f = Re (G σ) · e^{-σ u}`. Measurability of `u`
comes from `measurable_logDet`. Then:

* Landau's theorem `LandauMellin.integrable_of_differentiableOn` gives real integrability at
  every `σ > σ₀`, and `LandauMellin.integrable_bilateral` gives complex integrability.
* `LandauMellin.differentiableOn_bilateral`, applied to the restricted measure
  `ν.restrict A`, gives holomorphy of every partial integral.
* The real-point statements use `integral_complex_ofReal`, `setIntegral_mono_set` and
  `integral_pos_iff_support_of_nonneg`. They also use that `exp` never vanishes, so the
  support of `f e^{σu}` is the support of `f`.
