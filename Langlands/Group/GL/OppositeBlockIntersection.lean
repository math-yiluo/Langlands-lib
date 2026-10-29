import Langlands.Group.GL.OppositeBlocks

/-! # Opposite parabolics and upper block radicals -/

namespace Langlands.GeneralLinear.BlockShape

universe u

variable {n : ℕ} (B : BlockShape n) (R : Type u) [CommRing R]

/-- The lower block parabolic meets the upper block radical trivially. -/
theorem eq_one_of_mem_oppositeParabolic_of_mem_unipotentSubgroup
    {g : GeneralLinear n R} (hP : g ∈ B.oppositeParabolic R)
    (hU : g ∈ B.unipotentSubgroup R) : g = 1 := by
  rw [B.mem_oppositeParabolic_iff] at hP
  rw [B.mem_unipotentSubgroup_iff, B.mem_parabolic_iff] at hU
  obtain ⟨hU, hD⟩ := hU
  apply Units.ext
  ext r s
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective r
  obtain ⟨⟨j, b⟩, rfl⟩ := B.indexEquiv.surjective s
  change g (B.index i a) (B.index j b) =
    (1 : Matrix (Fin n) (Fin n) R) (B.index i a) (B.index j b)
  rcases lt_trichotomy i j with h | rfl | h
  · rw [hP i j a b h, Matrix.one_apply_ne]
    intro he
    exact (ne_of_lt h) (congrArg Sigma.fst
      (B.indexEquiv.injective (show B.indexEquiv ⟨i, a⟩ = B.indexEquiv ⟨j, b⟩ from he)))
  · rw [hD i a b]
    by_cases hab : a = b
    · subst hab
      simp
    · simp [hab, Matrix.one_apply_ne ((B.index i).injective.ne hab)]
  · rw [hU i j a b h, Matrix.one_apply_ne]
    intro he
    exact (ne_of_lt h) (congrArg Sigma.fst
      (B.indexEquiv.injective (show B.indexEquiv ⟨i, a⟩ = B.indexEquiv ⟨j, b⟩ from he))).symm

theorem oppositeUnipotentSubgroup_le_oppositeParabolic :
    B.oppositeUnipotentSubgroup R ≤ B.oppositeParabolic R := by
  rintro _ ⟨h, -, rfl⟩
  exact h.property

theorem leviSubgroup_le_oppositeParabolic :
    B.leviSubgroup R ≤ B.oppositeParabolic R := by
  rintro _ ⟨m, rfl⟩
  exact (B.oppositeLeviInParabolic R m).property

end Langlands.GeneralLinear.BlockShape

