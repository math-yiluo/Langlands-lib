import Langlands.Analysis.Meromorphic.AnalyticSystems
import Langlands.Analysis.Meromorphic.ManifoldIdentity

/-! # Holomorphy of `s ↦ φ (μ s (w s))`

Bernstein–Lapid §3.2: if `μ` is a holomorphic family of continuous linear
operators `V → F` on a complex manifold, `w` is a (weakly) holomorphic function
with values in `V` and `φ` is a continuous linear form on `F`, then
`s ↦ φ (μ s (w s))` is holomorphic. In a chart, `G x y = φ (μ x (w y))` is
holomorphic in each variable separately, so its diagonal is holomorphic by
Hartogs's theorem on separate holomorphy. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis.Meromorphic

open Set Filter Topology
open scoped Manifold

/-- Hartogs's theorem on separate holomorphy in the diagonal form used here:
on an open set `U` of `E`, a function of two variables that is complex
differentiable on `U` in each variable separately has a complex differentiable
diagonal. -/
def HartogsDiagonal (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E] : Prop :=
  ∀ (U : Set E) (G : E → E → ℂ), IsOpen U →
    (∀ t ∈ U, DifferentiableOn ℂ (fun s => G s t) U) →
    (∀ s ∈ U, DifferentiableOn ℂ (G s) U) → DifferentiableOn ℂ (fun s => G s s) U

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) 1 M]
  {V : Type*} [AddCommGroup V] [Module ℂ V] [TopologicalSpace V]
  {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]

/-- Bernstein–Lapid §3.2: for a holomorphic family `μ` of operators and a
holomorphic `w` on an open set `W`, the scalar function `s ↦ φ (μ s (w s))` is
holomorphic on `W`. -/
theorem mdifferentiableOn_apply_apply (hH : HartogsDiagonal E) {μ : M → V →L[ℂ] F}
    {w : M → V} {W : Set M} (hW : IsOpen W)
    (hμ : IsHolomorphicOperatorFamilyOn 𝓘(ℂ, E) μ W) (hw : IsHolomorphicOn 𝓘(ℂ, E) w W)
    (φ : F →L[ℂ] ℂ) :
    MDifferentiableOn 𝓘(ℂ, E) 𝓘(ℂ, ℂ) (fun s => φ (μ s (w s))) W := by
  intro s₀ hs₀
  set e := chartAt E s₀ with he
  set B := e.target ∩ e.symm ⁻¹' W with hB
  have hBo : IsOpen B := isOpen_chartAt_target_inter s₀ hW
  let G : E → E → ℂ := fun x y => φ (μ (e.symm x) (w (e.symm y)))
  have h1 : ∀ t ∈ B, DifferentiableOn ℂ (fun x => G x t) B := fun t _ =>
    differentiableOn_comp_chartAt_symm s₀ (hμ (w (e.symm t)) φ)
  have h2 : ∀ x ∈ B, DifferentiableOn ℂ (G x) B := fun x _ =>
    differentiableOn_comp_chartAt_symm s₀ (hw (φ.comp (μ (e.symm x))))
  have hm := mdifferentiableOn_comp_chartAt s₀ (hH B G hBo h1 h2)
  have hs₀e : s₀ ∈ e.source := mem_chart_source E s₀
  have hN : e.source ∩ e ⁻¹' B ∈ 𝓝 s₀ := by
    refine (e.continuousOn.isOpen_inter_preimage e.open_source hBo).mem_nhds ⟨hs₀e, ?_⟩
    refine ⟨e.map_source hs₀e, ?_⟩
    simpa [mem_preimage, e.left_inv hs₀e] using hs₀
  refine ((hm.mdifferentiableAt hN).congr_of_eventuallyEq ?_).mdifferentiableWithinAt
  filter_upwards [hN] with s hs
  simp only [G, Function.comp_apply, ← he, e.left_inv hs.1]

end Langlands.Analysis.Meromorphic
