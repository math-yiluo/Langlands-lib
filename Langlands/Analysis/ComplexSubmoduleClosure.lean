import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.Module.Basic

/-! # Continuous complex annihilators detect a submodule closure -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Analysis

variable {E : Type*} [AddCommGroup E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [Module ℝ E] [Module ℂ E]
  [IsScalarTower ℝ ℂ E] [ContinuousSMul ℂ E] [LocallyConvexSpace ℝ E]

/-- Complex annihilators detect membership in a submodule's topological closure. -/
theorem mem_topologicalClosure_of_forall_complex_annihilator
    (S : Submodule ℂ E) (x : E)
    (h : ∀ ℓ : E →L[ℂ] ℂ, (∀ y ∈ S, ℓ y = 0) → ℓ x = 0) :
    x ∈ S.topologicalClosure := by
  by_contra hx
  obtain ⟨ℓ, c, hS, hxc⟩ :=
    RCLike.geometric_hahn_banach_closed_point (𝕜 := ℂ)
      (S.topologicalClosure.restrictScalars ℝ).convex
      S.isClosed_topologicalClosure hx
  have hzero : ∀ y ∈ S.topologicalClosure, ℓ y = 0 := by
    intro y hy
    by_contra hne
    have hb := hS ((((c + 1 : ℝ) : ℂ) / ℓ y) • y)
      (S.topologicalClosure.smul_mem _ hy)
    simp only [map_smul, smul_eq_mul, div_mul_cancel₀ _ hne] at hb
    change c + 1 < c at hb
    linarith
  have hxzero := h ℓ (fun y hy => hzero y (S.le_topologicalClosure hy))
  have hc := hS 0 S.topologicalClosure.zero_mem
  simp only [map_zero] at hc
  simp only [hxzero, map_zero] at hxc
  linarith

end Langlands.Analysis
