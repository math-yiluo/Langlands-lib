# Holomorphy of parametric integrals in several complex variables

Module `Langlands.Analysis.SeveralComplex.ParametricIntegral` (namespace
`Langlands.Analysis.SeveralComplex`). It states and proves the proposition
`ParametricIntegralHolomorphyStatement` (proof `parametricIntegralHolomorphy`)
and the lemmas below. Everything is proved; there are no premises.

## Purpose and provenance

Helper for Lapid 2011, Proposition 6. Mathlib at the pinned
commit proves analyticity and Cauchy estimates for holomorphic functions of
one complex variable only. The proof of Proposition 6 needs holomorphy in several variables of
integrals such as averages `μ(N)⁻¹ ∫_N h(s, y) dμ(y)` over a set of group
elements and Cauchy integrals along circles. This module supplies the
standard criterion (dominated differentiation under the integral sign, with
the dominating bound on the derivative obtained from Cauchy's estimate).

Provenance: internal; standard complex analysis (Cauchy's inequality for the
derivative, differentiation under the integral sign), proved here from the
one-variable Cauchy estimate `Complex.norm_deriv_le_of_forall_mem_sphere_norm_le`
and Mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le`. On
`Fin n → ℂ` the norm is the sup norm, so balls are polydiscs.

## Statement

`ParametricIntegralHolomorphyStatement`: for `n : ℕ`, a measurable space
`α : Type`, a finite measure `μ` on `α`, `F : (Fin n → ℂ) → α → ℂ` and an
open `W ⊆ ℂⁿ`, if

1. `s ↦ F s a` is complex differentiable on `W` for every `a`,
2. `F s` is almost everywhere strongly measurable for every `s ∈ W`, and
3. for every compact `K ⊆ W` there is `C` with `‖F s a‖ ≤ C` for all `s ∈ K`
   and all `a`,

then `s ↦ ∫ a, F s a ∂μ` is complex differentiable on `W`. The theorem
`differentiableOn_integral_of_bounded` has the same content for
`α : Type*`.

## Proof

- `norm_fderiv_apply_le` (Cauchy estimate): if `f` is differentiable on an open
  `W ⊇ closedBall s r` and `‖f‖ ≤ C` on that ball, then
  `‖f'(s) v‖ ≤ C / r · ‖v‖`. For `v ≠ 0` apply the one-variable estimate to
  `z ↦ f(s + z v)` on the disc of radius `r / ‖v‖`, which maps into
  `closedBall s r`; its derivative at `0` is `f'(s) v` by the chain rule.
  `norm_fderiv_le` is the operator-norm form `‖f'(s)‖ ≤ C / r`.
- `continuousLinearMap_eq_sum`: a linear form `L` on `ℂⁿ` equals
  `∑ j, L(e_j) • proj_j` (`LinearMap.pi_apply_eq_sum_univ`).
- `aestronglyMeasurable_fderiv`: if `F s` is a.e. strongly measurable for `s`
  in a ball around `s₀` and every `F · a` is differentiable at `s₀`, then
  `a ↦ (F · a)'(s₀)` is a.e. strongly measurable. Each `a ↦ (F · a)'(s₀) e_j`
  is the pointwise limit of the difference quotients
  `t_k⁻¹ (F(s₀ + t_k e_j) a − F(s₀) a)`, `t_k = r / (k + 2)`
  (`HasDerivAt.tendsto_slope`, `aestronglyMeasurable_of_tendsto_ae`); the
  derivative is the finite sum `∑ j, (F · a)'(s₀) e_j • proj_j`.
- `differentiableOn_integral_of_bounded`: at `s₀ ∈ W` choose `r > 0` with
  `closedBall s₀ (2r) ⊆ W` and a bound `C` of `F` on it. For `s` in
  `ball s₀ r`, `closedBall s r ⊆ closedBall s₀ (2r)`, so
  `‖(F · a)'(s)‖ ≤ max C 0 / r` for all `a`. This constant is integrable for
  the finite measure `μ`, `F s₀` is integrable (bounded and measurable), and
  `hasFDerivAt_integral_of_dominated_of_fderiv_le` gives the derivative of the
  integral at `s₀`.

## Scope

Only scalar-valued integrands on `ℂⁿ` with a finite measure and a uniform
bound on compact sets are treated.
