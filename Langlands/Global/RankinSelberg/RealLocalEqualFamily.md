# Holomorphy of real equal-rank integrals in Whittaker families

This module is the real counterpart of the published complex module `ComplexLocalEqualFamily`.
It shows that the real equal-rank Rankin–Selberg integral
`realEqualIntegral D W V Φ s = ∫ W(g) V(g) Φ(e_n g) |det g|^s` (over the left unipotent quotient
`N \ GL_{r+1}(ℝ)`, with the quotient measure of `D`) depends holomorphically on a finite-dimensional
complex parameter. The parameter enters `W`, `V` and `s`, and the coefficients obey uniform gauge
estimates.

## Lemma

`integrable_realToralMajorant`: let a measure `ν` on the real left unipotent quotient have toral
marginal `κ exp(L y) dy` in the Iwasawa coordinate `alphaQ`. This is the form provided by the
Library's `exists_lintegral_alphaQ`. Then `q ↦ exp(-∑_j |y_j| - L y)`, with `y = alphaQ q`, is
`ν`-integrable. The density `exp(L y)` cancels and `exp(-∑ |y_j|)` is Lebesgue integrable. This is
the real version of `ComplexUnequalFamily.integrable_toralMajorant`.

## Statement

`RealLocalEqualFamilyStatement r E` concerns a finite-dimensional complex normed space `E`, an
open set `S ⊆ E`, two families `W, V : E → GL_{r+1}(ℝ) → ℂ`, a holomorphic `s : E → ℂ`, a Schwartz
function `Φ` on `ℝ^{r+1}` and a nonzero real `a`. It assumes:

* `W p` has the left upper unipotent character of `a` and `V p` that of `-a`
  (Worker 1050's `RealUnequalFamily.HasLeftCharacter`);
* every `W p` and `V p` is continuous;
* `p ↦ W p g` and `p ↦ V p g` are holomorphic on `S` for every `g`;
* both families satisfy `HasUniformGauge S`, the gauge estimate of `RealEqualConvergence.HasGauge`
  with constants uniform for `p ∈ S` (Worker 1050's `RealUnequalFamily.HasUniformGauge`).

It concludes that there is `σ` such that, on `S ∩ {σ < Re s(p)}`, the integrand
`realEqualIntegrand (W p) (V p) Φ (s p)` is integrable and
`p ↦ realEqualIntegral D (W p) (V p) Φ (s p)` is holomorphic.

## Proof

The proof follows the Library's single-function theorem `RealEqualConvergence.exists_convergence`,
with the constants made uniform, and the complex family argument.

1. The two left characters cancel (`realWhittakerCharacter_mul_neg`), so
   `kernel (W p) (V p) Φ = W(g) V(g) Φ(e_n g)` and `logDet` are left `N`-invariant. They descend to
   continuous functions on the quotient. The integrand is `kernel(q.out) · exp(s · logDet q.out)`.
2. Domination: put `A = N₁ + N₂ + ‖L‖`, with `N₁, N₂` the growth exponents of the two uniform
   gauges, and `σ = (A + 1)(r + 1)`. Given `τ`, choose
   `M = ⌈(A + 1)(r + 1) + τ (r + 1)⌉`. On `q = N torus(y) k`:
   * `W p` is bounded by the gauge with decay `M`;
   * `V p` is bounded by the gauge with decay `0`;
   * `Φ(e_n g)` is bounded by `exists_norm_le_exp` with decay `M` in `max(y_last, 0)`.

   For `σ < Re s ≤ τ`, the Library inequality `RealConvergenceAnalysis.exponent_le`, together with
   `L y ≤ ‖L‖ ∑ |y_j|`, bounds the total exponent by `-∑ |y_j| - L y`. This gives the
   parameter-independent integrable majorant `C exp(-∑ |y_j| - L y)` of the lemma.
3. The generic theorem `ComplexUnequalFamily.differentiableOn_integral_of_halfPlaneDomination`
   (measure-agnostic, in the published `ComplexUnequalOrdinaryFamily`) then gives integrability
   and holomorphy. Its inputs are measurability (continuity on the quotient), holomorphy of the
   integrand in `p` for each `q`, and the half-plane domination.

## Provenance and scope

This is a technical step for Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §8.1,
pp. 53–54, and §8.2. There the integrals of holomorphic families of Whittaker functions in the
inducing exponents are holomorphic on a common half-plane. The statement asserts holomorphy of
convergent integrals only. It proves no continuation or functional equation and does not prove
`RealLocalUniformPositiveEqualContinuationStatement`. `HasUniformGauge` and `HasLeftCharacter` come
from Worker 1050's accepted module `RealUnequalFamilyGauge`, whose unchanged pair accompanies this
candidate.
