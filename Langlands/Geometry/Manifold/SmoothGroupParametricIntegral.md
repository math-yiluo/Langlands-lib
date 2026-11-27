# Differentiation under the integral sign on a Lie group

Module `Langlands.Geometry.Manifold.SmoothGroupParametricIntegral`, namespace
`Langlands.Geometry.Manifold`. Throughout, `E` is a finite-dimensional real normed space and `G` a
Lie group with charted space `E` and model `𝓘(ℝ, E)`, smooth of order `∞`. The invariant derivative
`groupDirectionalValue 𝓘(ℝ, E) X f g` is the derivative at the identity of `h ↦ f (g * h)` in the
direction `X` of the identity tangent space (module `SmoothGroupDifferential`).

## Declarations

- `hasDerivAt_chartCurve u hu x₀ X`: for smooth `u : G → ℂ`, the function
  `t ↦ u (x₀ * e⁻¹(e 1 + t • X))`, where `e = extChartAt 𝓘(ℝ, E) 1`, has derivative
  `groupDirectionalValue 𝓘(ℝ, E) X u x₀` at `t = 0`.
- `aestronglyMeasurable_groupDirectionalValue`: let `μ` be a measure on `Ω` and `u : Ω → G → ℂ`
  with every `u x` smooth and every `x ↦ u x g` almost everywhere strongly measurable. Then
  `x ↦ groupDirectionalValue 𝓘(ℝ, E) X (u x) x₀` is almost everywhere strongly measurable.
- `contMDiff_integral_of_dominated_invariantDerivatives`: let `f : A → Ω → G → ℂ` and
  `step : GroupLieAlgebra 𝓘(ℝ, E) G → A → A` be such that every `f a x` is smooth,
  `groupDirectionalValue 𝓘(ℝ, E) X (f a x) = f (step X a) x`, every `x ↦ f a x g` is almost
  everywhere strongly measurable, and for every `a` and `g₀` there are a neighbourhood `U` of `g₀`
  and an integrable `bound` with `‖f a x g‖ ≤ bound x` for all `x` and all `g ∈ U`. Then every
  `g ↦ ∫ x, f a x g ∂μ` is smooth, and its invariant derivative in direction `X` is
  `g ↦ ∫ x, f (step X a) x g ∂μ`.

## Proofs

`hasDerivAt_chartCurve`. The private lemma `fderiv_chart_leftTranslate` identifies the derivative of
`(h ↦ u (x₀ * h)) ∘ e⁻¹` at `e 1` in direction `X` with the invariant derivative, by the chain rule
for manifold derivatives (`mvfderiv_comp_apply_of_eq`) and the fact that the derivative of `e⁻¹` at
`e 1` is the identity (`mfderivWithin_range_extChartAt_symm`). The function in chart coordinates is
differentiable at `e 1` because `u` and `e⁻¹` are smooth there, and composing with the line
`t ↦ e 1 + t • X` (`HasFDerivAt.comp_hasDerivAt_of_eq`) gives the derivative at `0`.

`aestronglyMeasurable_groupDirectionalValue`. By `hasDerivAt_chartCurve` and
`hasDerivAt_iff_tendsto_slope`, the invariant derivative is the limit of the slopes at the points
`1 / (n + 1)`, which tend to `0` within `{0}ᶜ`. Each slope is a scalar multiple of a difference of
two measurable functions of `x`, so `aestronglyMeasurable_of_tendsto_ae` applies.

`contMDiff_integral_of_dominated_invariantDerivatives`. Let `I a g = ∫ x, f a x g ∂μ`. The private
lemma `hasFDerivAt_integral_of_expansion` works in a smooth parametrization `ψ` of an open set `S`
of `E`, with the invariant frame of `exists_invariantDerivativeExpansion` (module
`SmoothGroupChartDerivative`): directions `X j` and smooth coefficient maps `L j` such that every
smooth `u` satisfies `HasFDerivAt (u ∘ ψ) (∑ j, (L j y).smulRight (groupDirectionalValue (X j) u (ψ y))) y`.
At `y₀ ∈ S` it takes the neighbourhood on which `ψ y` lies in the domination neighbourhoods of all
`f (step (X j) a)` at `ψ y₀` and `‖L j y‖ < ‖L j y₀‖ + 1`. There the derivatives of the integrands
are bounded by `∑ j, (‖L j y₀‖ + 1) * bound_j`. Mathlib's
`hasFDerivAt_integral_of_dominated_of_fderiv_le` then gives
`HasFDerivAt (I a ∘ ψ) (∑ j, (L j y₀).smulRight (I (step (X j) a) (ψ y₀))) y₀`, after exchanging the
integral with the finite sum and with the continuous linear maps `smulRightL`.

The rest follows the proof of `contMDiff_of_tendstoLocallyUniformly_invariantDerivatives` (module
`SmoothGroupUniformLimit`). By induction on `n`, every `I a ∘ ψ` is `C^n` on `S`: continuity comes
from differentiability, and the derivative is a finite sum of smooth coefficients times functions
`I (step (X j) a) ∘ ψ` of class `C^n` by induction. Applied to the inverse extended charts this gives
smoothness of every `I a`. For the derivative formula, put `ψ y = x₀ * e⁻¹ y` and compare at `e 1`:
`fderiv_chart_leftTranslate` turns the chart derivative of `I a` into its invariant derivative, the
expansion expresses it through the `I (step (Y j) a) x₀`, and the same expansion applied to each
`f a x` together with the derivative relation of the integrands identifies the integrand of
`I (step X a) x₀` with the corresponding combination.

## Provenance

The module is internal. It formalizes differentiation under the integral sign with dominated
derivatives. The Library uses it to prove the smoothness of the intertwining integrals of
Mœglin–Waldspurger, *Spectral decomposition and Eisenstein series* (1995), II.1.6, Proposition (i),
printed pp. 87–88, which asserts that these integrals define automorphic forms; the proof given there
on p. 88 concerns convergence and does not differentiate under the integral.
