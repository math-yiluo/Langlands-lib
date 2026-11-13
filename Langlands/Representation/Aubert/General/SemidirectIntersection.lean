import Langlands.Representation.Aubert.General.Parabolic

/-! # The intersection in a semidirect decomposition -/

namespace Langlands.Aubert.General.RepresentedParabolic

variable {Γ : Type*} [Group Γ]

/-- In a semidirect decomposition the Levi and unipotent subgroups meet trivially. -/
theorem IsSemidirectDecomposition.eq_one_of_mem_of_mem {P M U : Subgroup Γ}
    (h : IsSemidirectDecomposition P M U) {x : Γ} (hM : x ∈ M) (hU : x ∈ U) : x = 1 := by
  have h1 := h.projection_levi ⟨x, hM⟩
  have h2 := (h.projection_eq_one_iff ⟨x, h.levi_le hM⟩).mpr hU
  rw [h1] at h2
  exact congrArg Subtype.val h2

end Langlands.Aubert.General.RepresentedParabolic
