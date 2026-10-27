# Proof: compact integration of a smooth linear-parameter family

This module proves the published proposition
`Langlands.Analysis.CompactLinearParameterIntegralStatement` (module
`Langlands.Analysis.CompactLinearParameterIntegralStatement`) as the theorem

```
Langlands.Analysis.compactLinearParameterIntegral :
    CompactLinearParameterIntegralStatement.{uY, uV, uW}
```

with the statement's three independent universe parameters and no additional
hypotheses. In the notation of the statement, for every Hausdorff Borel space
`Y`, measure `μ` finite on compact sets, compact `k ⊆ Y`, open `s ⊆ V` and
`t ⊆ W`, continuous `f : Y → ℂ` and `A : Y → V →L[ℝ] W`, and `φ` real `C^∞`
on `t` with `A y x ∈ t` for `y ∈ k`, `x ∈ s`, the function
`F x = ∫ y in k, f y * φ (A y x) ∂μ` is `C^∞` on `s`, and at every `x ∈ s` its
Fréchet derivative is `∫ y in k, (f y) • ((fderiv ℝ φ (A y x)).comp (A y)) ∂μ`.
Empty `k`, the zero measure and zero-dimensional spaces are covered because
nothing in the proof excludes them.

## Strategy

The proof works with a more general *affine* integrand. Fix `Y`, `V`, `μ`,
`k`, `s` and `f`. For a real normed space `W`, an open `t ⊆ W`, a continuous
`A : Y → V →L[ℝ] W`, a continuous offset `c : Y → W` and `ψ : W → ℂ` that is
`C^∞` on `t`, with `A y x + c y ∈ t` for `y ∈ k`, `x ∈ s`, consider

```
G x = ∫ y in k, f y * ψ (A y x + c y) ∂μ.
```

The statement is the case `c = 0`, `ψ = φ`. The point of the offset is that
directional derivatives of such integrals are again integrals of the same
shape, over the space `W × W`. So an induction on the smoothness order never
changes the codomain `ℂ` of the integral, and the varying space `W × W` stays in
the universe of `W`; no universe transport is needed.

## Auxiliary lemmas (namespace `Langlands.Analysis.CompactLinearParameterIntegral`)

- `continuousOn_partialDeriv`: the partial derivative
  `p ↦ (f p.1) • ((fderiv ℝ ψ (A p.1 p.2 + c p.1)).comp (A p.1))` is
  continuous on `k ×ˢ s`. The point `(y, x) ↦ A y x + c y` is continuous
  (`Continuous.clm_apply`) and maps `k ×ˢ s` into `t`; `fderiv ℝ ψ` is
  continuous on the open set `t` by `contDiffOn_infty_iff_fderiv_of_isOpen`;
  composition with `A y` (`ContinuousOn.clm_comp`) and the scalar `f y`
  (`ContinuousOn.smul`) preserve continuity.
- `continuousOn_integrand`: for `x ∈ s`, `y ↦ f y * ψ (A y x + c y)` is
  continuous on `k`.
- `hasFDerivAt_integral`: for `x₀ ∈ s`, `G` has Fréchet derivative
  `∫ y in k, (f y) • ((fderiv ℝ ψ (A y x₀ + c y)).comp (A y)) ∂μ` at `x₀`.
  This applies Mathlib's `hasFDerivAt_integral_of_dominated_of_fderiv_le` to
  the measure `μ.restrict k`, with the explicit partial derivative above and a
  constant bound `C`. The bounds are derived, not assumed: choose `ε > 0` with
  `ball x₀ ε ⊆ s`; then `closedBall x₀ (ε / 2) ⊆ s` is compact because `V` is
  finite-dimensional, so `k ×ˢ closedBall x₀ (ε / 2)` is compact and the
  jointly continuous partial derivative is bounded there by some `C`
  (`IsCompact.exists_bound_of_continuousOn`). This bounds it for all
  `y ∈ k` and all `x` in `ball x₀ (ε / 2)`. The constant `C` is integrable on
  `k` because `μ k < ∞` (`IsCompact.measure_lt_top`, `integrableOn_const`).
  Measurability and integrability of the integrand and of the partial
  derivative at `x₀` come from continuity on the compact, measurable set `k`
  (`ContinuousOn.aestronglyMeasurable_of_isCompact`,
  `ContinuousOn.integrableOn_compact`); the a.e. statements on `μ.restrict k`
  come from statements for every `y ∈ k` (`ae_restrict_of_forall_mem`). The
  pointwise derivative for `y ∈ k` is the chain rule for `ψ` at
  `A y x + c y ∈ t` (differentiable there because `t` is open) composed with
  the affine map `x ↦ A y x + c y`, multiplied by the constant `f y`
  (`HasFDerivAt.const_mul`).
- `contDiffOn_integral_nat`: for every `n : ℕ`, and for all `W` (in a fixed
  universe), `t`, `A`, `c`, `ψ` as above, `G` is `C^n` on `s`. Induction on
  `n`, with all of `W`, `t`, `A`, `c`, `ψ` generalized:
  - `n = 0`: `G` is differentiable at every point of `s` by
    `hasFDerivAt_integral`, hence continuous on `s`.
  - `n + 1`: by `contDiffOn_succ_of_fderiv_apply` (finite-dimensional `V`) it
    suffices that `G` is differentiable on `s` and that for every direction
    `v`, `x ↦ fderivWithin ℝ G s x v` is `C^n` on `s`. On the open set `s`,
    `fderivWithin` is `fderiv`, which is the integral from
    `hasFDerivAt_integral`; applying it to `v` commutes with the integral
    (`ContinuousLinearMap.integral_apply`, using integrability from
    continuity on `k`), giving
    `∫ y in k, f y * fderiv ℝ ψ (A y x + c y) (A y v) ∂μ`. This is the
    affine integrand for the space `W × W`, the open set `t ×ˢ univ`, the
    function `Ψ p = fderiv ℝ ψ p.1 p.2`, the maps
    `y ↦ (ContinuousLinearMap.inl ℝ W W).comp (A y)` and the offsets
    `y ↦ (c y, A y v)`, since
    `(A y x, 0) + (c y, A y v) = (A y x + c y, A y v)`. The map `Ψ` is
    `C^∞` on `t ×ˢ univ` because `fderiv ℝ ψ` is `C^∞` on the open set `t`
    (`contDiffOn_infty_iff_fderiv_of_isOpen`) and evaluation of a continuous
    linear map is smooth (`ContDiffOn.clm_apply`); the new maps and offsets
    are continuous. The induction hypothesis therefore gives the required
    `C^n` regularity.

## The main theorem

`compactLinearParameterIntegral` takes the statement's data, applies the
auxiliary lemmas with the zero offset `c = fun _ => 0` and `ψ = φ`, and
removes `+ 0` by simplification. The `C^∞` part follows from
`contDiffOn_integral_nat` for every `n` and `contDiffOn_infty`; the derivative
part is `hasFDerivAt_integral` at each `x ∈ s`, which is exactly the
derivative `∫ y in k, (f y) • ((fderiv ℝ φ (A y x)).comp (A y)) ∂μ` required
by the statement.

## Provenance

This is internal, standard parametric-integral analysis written for this
project; it quotes no literature and reuses no draft proof material (the
statement's author supplied no proof draft). The first derivative is Mathlib's
dominated differentiation theorem
`hasFDerivAt_integral_of_dominated_of_fderiv_le`
(`Mathlib/Analysis/Calculus/ParametricIntegral.lean`), with the local uniform
bound derived from compactness as described above. The induction on the order
differs from the model suggested in the statement's Markdown
(`contDiffOn_convolution_right_with_param` in
`Mathlib/Analysis/Calculus/ContDiff/Convolution.lean`, which changes the
derivative codomain and transports universes): here it uses directional
derivatives through `contDiffOn_succ_of_fderiv_apply`
(`Mathlib/Analysis/Calculus/ContDiff/FiniteDimension.lean`), so the codomain
stays `ℂ` and only the auxiliary space `W` changes, to `W × W`.
