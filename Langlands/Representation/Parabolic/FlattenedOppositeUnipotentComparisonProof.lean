import Langlands.Representation.Parabolic.FlattenedOppositeJacquetComparisonStatement

/-! Equality of the actual composed and flattened opposite radicals. -/

namespace Langlands.Parabolic

open GeneralLinear Geometric
open GeneralLinear.BlockShape

universe uK

variable (K : Type uK) [CommRing K] {n : ℕ} (B : BlockShape n)
    (S : BlockRefinement B)

private theorem flattened_le_composed :
    (B.flatten S).oppositeUnipotentSubgroup K ≤ composedOppositeUnipotent K B S := by
  intro g hg
  obtain ⟨hgP, hgD⟩ := ((B.flatten S).mem_oppositeUnipotentSubgroup_iff K g).mp hg
  rw [(B.flatten S).mem_oppositeParabolic_iff] at hgP
  have hcoord : ∀ (i : Fin B.length) (a : Fin (B.size i)),
      ∃ (j : Fin (S i).length) (c : Fin ((S i).size j)), a = (S i).index j c := by
    intro i a
    obtain ⟨⟨j, c⟩, rfl⟩ := (S i).indexEquiv.surjective a
    exact ⟨j, c, rfl⟩
  have hB : g ∈ B.oppositeParabolic K := by
    rw [B.mem_oppositeParabolic_iff]
    intro i i' a b hii'
    obtain ⟨j, c, rfl⟩ := hcoord i a
    obtain ⟨j', c', rfl⟩ := hcoord i' b
    rw [B.index_index_eq_flatten S ⟨i, j⟩ c,
      B.index_index_eq_flatten S ⟨i', j'⟩ c']
    apply hgP
    exact (B.flattenBlockEquiv_lt_iff S _ _).mpr (Or.inl hii')
  refine (mem_oppositeLeviPreimage_iff K B _ g).mpr ⟨hB, ?_⟩
  rw [mem_refinedOppositeUnipotent]
  intro i
  rw [(S i).mem_oppositeUnipotentSubgroup_iff, (S i).mem_oppositeParabolic_iff]
  refine ⟨fun j j' a b hjj' => ?_, fun j a b => ?_⟩
  · rw [oppositeLeviProjection_apply]
    dsimp only
    rw [B.index_index_eq_flatten S ⟨i, j⟩ a,
      B.index_index_eq_flatten S ⟨i, j'⟩ b]
    apply hgP
    exact (B.flattenBlockEquiv_lt_iff S _ _).mpr (Or.inr ⟨rfl, hjj'⟩)
  · rw [oppositeLeviProjection_apply]
    dsimp only
    rw [B.index_index_eq_flatten S ⟨i, j⟩ a,
      B.index_index_eq_flatten S ⟨i, j⟩ b, hgD]
    simp only [Fin.cast_inj]

private theorem composed_le_flattened :
    composedOppositeUnipotent K B S ≤ (B.flatten S).oppositeUnipotentSubgroup K := by
  intro g hg
  obtain ⟨hB, hI⟩ := (mem_oppositeLeviPreimage_iff K B _ g).mp hg
  have hinner := (mem_refinedOppositeUnipotent K B S _).mp hI
  have hBzero := (B.mem_oppositeParabolic_iff K g).mp hB
  have hzero : ∀ (i i' : Fin B.length) (j : Fin (S i).length)
      (j' : Fin (S i').length) (a : Fin ((S i).size j))
      (b : Fin ((S i').size j')),
      i < i' ∨ (i = i' ∧ j.val < j'.val) →
        g (B.index i ((S i).index j a)) (B.index i' ((S i').index j' b)) = 0 := by
    intro i i' j j' a b hij
    rcases hij with hii' | ⟨rfl, hjj'⟩
    · exact hBzero i i' _ _ hii'
    · have hi := ((S i).mem_oppositeUnipotentSubgroup_iff K _).mp (hinner i)
      have hz := ((S i).mem_oppositeParabolic_iff K _).mp hi.1 j j' a b hjj'
      simpa only [oppositeLeviProjection_apply] using hz
  apply ((B.flatten S).mem_oppositeUnipotentSubgroup_iff K g).mpr
  constructor
  · rw [(B.flatten S).mem_oppositeParabolic_iff]
    intro k k' a b hkk'
    rw [B.flatten_index S k a, B.flatten_index S k' b]
    apply hzero
    apply (B.flattenBlockEquiv_lt_iff S _ _).mp
    simpa only [Equiv.apply_symm_apply] using hkk'
  · intro k a b
    rw [B.flatten_index S k a, B.flatten_index S k b]
    have hi := ((S ((B.flattenBlockEquiv S).symm k).1).mem_oppositeUnipotentSubgroup_iff
      K _).mp (hinner ((B.flattenBlockEquiv S).symm k).1)
    exact hi.2 ((B.flattenBlockEquiv S).symm k).2 a b

/-- The inverse-image opposite radical is the standard radical of the actual
ordered flattened block shape. -/
theorem flattenedOppositeUnipotentComparison :
    FlattenedOppositeUnipotentComparisonStatement.{uK} := by
  intro K _ n B S
  exact le_antisymm (composed_le_flattened K B S) (flattened_le_composed K B S)

end Langlands.Parabolic
