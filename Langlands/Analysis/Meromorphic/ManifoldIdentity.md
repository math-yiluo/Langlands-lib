# Charts, the identity theorem and separation by complex linear forms

Module `Langlands.Analysis.Meromorphic.ManifoldIdentity` collects auxiliary
facts for the proof of the principle of meromorphic continuation
(`Langlands.Analysis.Meromorphic.ContinuationPrincipleReduction`). It
defines one structure, `ChartBall`, and proves standard facts: separation of
points by continuous complex linear forms, the identity theorem on convex sets
and chart balls, and transfer of holomorphy through charts.

## Provenance

The module is internal. Bernstein–Lapid, *On the meromorphic continuation of
Eisenstein series*, J. Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, uses these facts
tacitly in Appendix A (pp.230–231; TeX `1911.02342.tex` lines 3817–3990): that continuous linear forms detect vectors
of a Hausdorff locally convex space, and that a holomorphic function on a
connected open set vanishing on a nonempty open subset vanishes identically.
Both are classical (Hahn–Banach, identity theorem). The formulations here suit
the Lean proof, and the Lean proofs are given in full.

## Separation

Let `F` be a complex vector space with a real structure compatible with the
complex one (`IsScalarTower ℝ ℂ F`), a topology making it a topological
additive group with continuous complex scalar multiplication, locally convex
over `ℝ` and `T₁`.

- `separatingDual_complex`: `SeparatingDual ℂ F`, i.e. for every `x ≠ 0` there
  is a continuous complex linear form `φ` with `φ x ≠ 0`. The proof applies
  Mathlib's complex geometric Hahn–Banach theorem for two points
  (`RCLike.geometric_hahn_banach_point_point`) to `x` and `0`.
- `eq_of_forall_clm_apply_eq`: if `φ x = φ y` for every continuous complex
  linear form `φ` on `F`, then `x = y`.

## Identity theorem on convex sets

`eqOn_zero_of_convex_of_eqOn_zero`: let `E` be a complex normed space, `B ⊆ E`
open and convex, `g : E → ℂ` complex differentiable on `B`, and `O ⊆ B` open
and nonempty with `g = 0` on `O`. Then `g = 0` on `B`.

Proof: fix `p ∈ O` and `x ∈ B`, and restrict `g` to the complex line
`L(z) = p + z (x - p)`. The set `D = L⁻¹(B) ⊆ ℂ` is open and convex, so
preconnected. `g ∘ L` is holomorphic on `D`, hence analytic there, and it
vanishes near `0` because `L(0) = p ∈ O`. The one-variable identity theorem
(`AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero`) gives
`g(L(1)) = g(x) = 0`.

## Charts

Let `M` be a manifold charted on a complex normed space `E` with
`IsManifold 𝓘(ℂ, E) 1 M`. "Holomorphic" for scalar functions on `M` means
`MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ)`.

- `differentiableOn_comp_chartAt_symm`: if `h` is holomorphic on `W ⊆ M`, then
  `h ∘ (chartAt E s₀).symm` is complex differentiable on
  `(chartAt E s₀).target ∩ (chartAt E s₀).symm ⁻¹' W`.
- `mdifferentiableOn_comp_chartAt`: if `g : E → ℂ` is complex differentiable on
  `B`, then `g ∘ chartAt E s₀` is holomorphic on
  `(chartAt E s₀).source ∩ chartAt E s₀ ⁻¹' B`.
- `isOpen_chartAt_target_inter`: the set
  `(chartAt E s₀).target ∩ (chartAt E s₀).symm ⁻¹' W` is open when `W` is.

Both transfer lemmas compose with the holomorphy of charts and inverse charts
of the atlas (`mdifferentiableOn_atlas`, `mdifferentiableOn_atlas_symm`).

## Chart balls

`ChartBall s₀ W` (a `Prop`-valued structure) says that there is an open
convex `B ⊆ (chartAt E s₀).target` with
`W = (chartAt E s₀).source ∩ chartAt E s₀ ⁻¹' B`, i.e. `W` is the preimage
under the chart at `s₀` of a convex open subset of the chart's target.

- `ChartBall.isOpen`, `ChartBall.subset_source`: `W` is open and lies in the
  chart's source.
- `ChartBall.isPreconnected`: `W` is the image of the convex set `B` under the
  continuous inverse chart, hence preconnected.
- `ChartBall.eqOn_zero` (identity theorem on a chart ball): if `h : M → ℂ` is
  holomorphic on `W` and vanishes on a nonempty open `O ⊆ W`, then `h = 0` on
  `W`. The proof moves `h` to the chart and applies the convex identity
  theorem to `B` and the open set `B ∩ (chartAt E s₀).symm ⁻¹' O`.
- `exists_chartBall_subset`: every neighbourhood `U` of `s₀` contains a chart
  ball `W` at `s₀` with `s₀ ∈ W`. One takes `B` a metric ball about the chart
  image of `s₀` inside the chart image of the interior of `U`.
