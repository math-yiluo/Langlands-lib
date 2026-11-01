import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! # Finite-dimensional intersections and continuous projections -/

noncomputable section
universe u v
set_option autoImplicit false

namespace Langlands.Analysis

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CompleteSpace 𝕜]
  {E : Type v} [AddCommGroup E] [TopologicalSpace E] [IsTopologicalAddGroup E]
  [Module 𝕜 E] [ContinuousSMul 𝕜 E] [T2Space E]

/-- A continuous projection preserving `M` prevents new vectors of `T` from
appearing in the closure of `M` when `M ⊓ T` is finite-dimensional. -/
theorem inf_topologicalClosure_eq_of_projection
    (M T : Submodule 𝕜 E) (P : E →L[𝕜] E)
    (h_range : ∀ x, P x ∈ T)
    (h_fix : ∀ x, x ∈ T → P x = x)
    (h_preserve : ∀ x, x ∈ M → P x ∈ M)
    [Module.Finite 𝕜 (M ⊓ T : Submodule 𝕜 E)] :
    M.topologicalClosure ⊓ T = M ⊓ T := by
  have h_closed :
      IsClosed (((M ⊓ T).comap P.toLinearMap : Submodule 𝕜 E) : Set E) :=
    (M ⊓ T).closed_of_finiteDimensional.preimage P.continuous
  have h_le : M ≤ (M ⊓ T).comap P.toLinearMap := by
    intro x hx
    exact ⟨h_preserve x hx, h_range x⟩
  have h_closure := M.topologicalClosure_minimal h_le h_closed
  ext x
  constructor
  · intro hx
    have hPx : P x ∈ M ⊓ T := h_closure hx.1
    rwa [h_fix x hx.2] at hPx
  · intro hx
    exact ⟨M.le_topologicalClosure hx.1, hx.2⟩

end Langlands.Analysis
