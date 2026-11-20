# Holomorphy of `s ↦ φ (μ s (w s))`, from Hartogs's theorem

Module `Langlands.Analysis.Meromorphic.WeakComposition` names Hartogs's theorem
on separate holomorphy as a proposition, `HartogsDiagonal E`. From it, the
module proves that applying a holomorphic family of operators to a holomorphic
vector-valued function gives a holomorphic function, in the weak sense of
`Langlands.Analysis.Meromorphic.AnalyticSystems`. Hartogs's theorem itself is
not proved here. It is the one named premise of this module and of the
modules built on it.

## Provenance

Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*, J.
Amer. Math. Soc. 37 (2024), registered as
`bernstein-lapid-2024-meromorphic-continuation-eisenstein`, §3.2 (p.193; TeX
`1911.02342.tex` lines 665–669). There, the composite of analytic families of
operators between Hausdorff locally convex spaces is analytic, which "follows
from Hartogs's Theorem on separate holomorphicity". For Hartogs's theorem the
source cites S. G. Krantz, *Function theory of several complex variables*
(AMS Chelsea, 2001), §0.2 and Theorem 1.2.5. The lemma here is the case needed in
Appendix A: an operator family applied to a holomorphic vector-valued
function. Its proof is the argument the source indicates.

## The premise `HartogsDiagonal`

`HartogsDiagonal E` (a `def` with value in `Prop`, for a complex normed space
`E`) says the following. Let `U ⊆ E` be open and `G : E → E → ℂ`. Suppose
`s ↦ G s t` is complex differentiable on `U` for every `t ∈ U`, and `G s` is
complex differentiable on `U` for every `s ∈ U`. Then the diagonal
`s ↦ G s s` is complex differentiable on `U`.

For finite-dimensional `E` this follows from Hartogs's theorem on separate
holomorphy. `G` restricted to `U × U` is separately holomorphic in the two
variables, hence jointly holomorphic, so its composite with the diagonal
embedding is holomorphic. The `def` asserts nothing by itself. It is used
only as a hypothesis, and only for finite-dimensional `E`. A proof of it for
every finite-dimensional `E` is being developed separately as
`Langlands.Analysis.SeveralComplex.differentiableOn_diag_of_separately`, with
the same hypotheses and conclusion.

## Statement

`mdifferentiableOn_apply_apply`: let `E` be a complex normed space with
`HartogsDiagonal E` (hypothesis `hH`). Let `M` be a manifold charted on `E`
with `IsManifold 𝓘(ℂ, E) 1 M`, let `V` and `F` be complex vector spaces with
topologies (no further assumptions), and let `W ⊆ M` be open. Let
`μ : M → V →L[ℂ] F` be a holomorphic family of operators on `W`
(`IsHolomorphicOperatorFamilyOn`: `s ↦ ψ (μ s v)` is holomorphic on `W` for
all `v` and all continuous linear forms `ψ`). Let `w : M → V` be holomorphic
on `W` (`IsHolomorphicOn`) and let `φ : F →L[ℂ] ℂ`. Then `s ↦ φ (μ s (w s))` is
holomorphic on `W`, i.e. `MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ)`.

## Proof

Fix `s₀ ∈ W`, write `e = chartAt E s₀`, and let `B = e.target ∩ e.symm ⁻¹' W`,
an open subset of `E`. Put `G x y = φ (μ (e.symm x) (w (e.symm y)))` for
`x, y ∈ E`.

- For fixed `y`, `x ↦ G x y` is the form `φ` applied to `μ (·) v` with
  `v = w (e.symm y)`. It is therefore complex differentiable on `B`
  (`differentiableOn_comp_chartAt_symm`).
- For fixed `x`, `y ↦ G x y` is the continuous linear form `φ ∘ μ (e.symm x)`
  applied to `w`. It is therefore complex differentiable on `B`.

`hH` applied to `B` and `G` shows that `x ↦ G x x` is complex differentiable
on `B`. Moving back to `M` (`mdifferentiableOn_comp_chartAt`),
`s ↦ G (e s) (e s)` is holomorphic on `e.source ∩ e ⁻¹' B`, a neighbourhood of
`s₀`. It agrees there with `s ↦ φ (μ s (w s))` because `e.symm (e s) = s`. So
the latter is holomorphic at `s₀`.
