# Compact integration of a smooth linear-parameter family

This internal statement isolates an analytic prerequisite for the actual
archimedean convolution problem. It is not a quotation from the
automorphic-form literature, and this module proves none of its content: it
only defines the proposition
`Langlands.Analysis.CompactLinearParameterIntegralStatement : Prop`.

## Hypotheses

The proposition quantifies, with three independent type universes `uY`, `uV`
and `uW`, over:

- an arbitrary Hausdorff topological space `Y` whose measurable structure is
  its Borel σ-algebra (`T2Space Y`, `BorelSpace Y`);
- real finite-dimensional normed spaces `V` (the parameter space) and `W`;
- every measure `μ` on `Y` that is finite on compact sets
  (`IsFiniteMeasureOnCompacts μ`); the zero measure is allowed;
- a compact set `k ⊆ Y` (possibly empty), an open set `s ⊆ V` and an open set
  `t ⊆ W`;
- a continuous complex weight `f : Y → ℂ`;
- a family `A : Y → V →L[ℝ] W` of real continuous linear maps that is
  continuous for the operator-norm topology;
- a function `φ : W → ℂ` that is real `C^∞` on `t`
  (`ContDiffOn ℝ ∞ φ t`, smooth of every finite order, not analytic);
- the compatibility hypothesis `A y x ∈ t` for every `y ∈ k` and `x ∈ s`.

No smoothness of `f` or `A`, no differentiability in the integration
variable `y`, no invariance of `μ`, no nonzero measure, nonempty set or
positive-dimensional space is assumed. Nothing is assumed about `φ` outside
`t`.

## Conclusion

Write `F x = ∫ y in k, f y * φ (A y x) ∂μ`, the complex Bochner integral over
`k`, that is, with respect to the restricted measure `μ.restrict k`. The
proposition asserts the conjunction of:

1. `ContDiffOn ℝ ∞ F s`: the integral is real `C^∞` on `s`;
2. for every `x ∈ s`, `HasFDerivAt F D x`, where
   `D = ∫ y in k, (f y) • ((fderiv ℝ φ (A y x)).comp (A y)) ∂μ`
   is the Bochner integral in `V →L[ℝ] ℂ`. Here `fderiv ℝ φ (A y x)` is the
   real Fréchet derivative `W →L[ℝ] ℂ` of `φ` at `A y x`, its composite with
   `A y` is the partial derivative in `x` of `x ↦ φ (A y x)`, and `f y •`
   multiplies the complex output of that real linear map by `f y`.

Thus the first derivative of the integral is the integral of the actual
partial derivative of the integrand.

## Provenance

The statement is internal and derived from standard analysis, not from a
cited source. Its intended proof is local: around each point of `s`, a closed
ball in the finite-dimensional space `V` contained in `s` is compact, so the
continuous map `(y, x) ↦ A y x` sends the product of `k` with that ball into a
compact subset of `t`. Continuity of `f`, `A` and the derivatives of `φ` on
`t` then gives uniform bounds on every parameter derivative of the integrand
over that compact set, and `μ k < ∞`. Mathlib's
`Mathlib/Analysis/Calculus/ParametricIntegral.lean`
(`hasFDerivAt_integral_of_dominated_of_fderiv_le`) supplies dominated
differentiation under the integral, and an induction on the smoothness order,
modelled on `contDiffOn_convolution_right_with_param` in
`Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`, upgrades the first
derivative to `C^∞`. A proof must supply those bounds and that induction; they
are not assumed here.

## Intended application

In the parent archimedean application, `Y` is the published completion-based
archimedean general linear group, `V = W` is its real matrix algebra, `A y`
is left multiplication by the matrix of `y⁻¹`, and `φ` is the published
coordinate extension of the smooth compact kernel on the open set of unit
matrices. Local compact support in the integration variable permits replacing
the raw convolution by this fixed compact integral. That application and its
direction computation are separate from this analytic statement.
