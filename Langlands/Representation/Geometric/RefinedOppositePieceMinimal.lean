import Langlands.Representation.Geometric.RefinedOppositePieceTransport

/-! Minimality of the actual inner and outer reversal coordinate for a whole piece. -/

noncomputable section

namespace Langlands.Geometric.RefinedOppositePieceTransport

open GeneralLinear CuspidalSupport ProductLeviDualOpposite
open OppositeCuspidalJacquetFiltration ProductLeviMinimalIndex

universe uF

variable {n : ℕ} (B : BlockShape n) (S : BlockRefinement B)

/-- Reversal reverses block labels and keeps each within-block coordinate. -/
theorem blockIndex_reversePermutation (C : BlockShape n) (a : Fin n) :
    blockIndex C (C.reversePermutation a) = (blockIndex C.reverse a).rev := by
  change (C.indexEquiv.symm
    (C.indexEquiv (C.reverseIndexEquiv (C.reverse.indexEquiv.symm a)))).1 =
      @Fin.rev C.length (C.reverse.indexEquiv.symm a).1
  rw [Equiv.symm_apply_apply]
  rfl

/-- Inverse reversal reverses the original block labels. -/
theorem blockIndex_reversePermutation_symm (C : BlockShape n) (a : Fin n) :
    blockIndex C.reverse (C.reversePermutation.symm a) = (blockIndex C a).rev := by
  have h := blockIndex_reversePermutation C (C.reversePermutation.symm a)
  rw [Equiv.apply_symm_apply] at h
  apply @Fin.rev_injective C.length
  rw [Fin.rev_rev]
  exact h.symm

/-- Inner reversal is a minimal whole-Levi conjugating permutation between
the reversed and original flattened shapes. -/
theorem isMinimalRepresentative_innerReverse :
    IsMinimalRepresentative (B.flatten (reverseRefinement B S)) (B.flatten S)
      (innerReversePermutation B S) := by
  rw [isMinimalRepresentative_iff]
  constructor
  · rw [forall_flatten_pairs_iff B (reverseRefinement B S)]
    intro i a b hab hlt
    simp only [innerReversePermutation, blockPermOf_index]
    apply index_strictMono B i
    exact reversePermutation_lt_of_blockIndex_eq (S i) hab
      ((index_strictMono B i).lt_iff_lt.mp hlt)
  · rw [forall_flatten_pairs_iff B S]
    intro i a b hab hlt
    simp only [innerReversePermutation, blockPermOf_symm_index]
    apply index_strictMono B i
    exact (strictMono_index_iff (S i) (S i).reversePermutation.symm).mp
      (reversePermutation_symm_index_strictMono (S i)) a b hab
      ((index_strictMono B i).lt_iff_lt.mp hlt)

/-- Refining only the source preserves minimality. -/
theorem isMinimalRepresentative_flatten_source {C : BlockShape n}
    {x : Equiv.Perm (Fin n)} (hmin : IsMinimalRepresentative B C x) :
    IsMinimalRepresentative (B.flatten S) C x := by
  rw [isMinimalRepresentative_iff] at hmin ⊢
  refine ⟨fun a b hab hlt => hmin.1 a b ?_ hlt, hmin.2⟩
  rw [blockIndex_eq_flatten B S a, blockIndex_eq_flatten B S b, hab]

variable {F : Type uF} [Field F] {C : BlockShape n}
  {x : Equiv.Perm (Fin n)}

/-- Minimality of the reversed coordinate for the fine source. -/
theorem isMinimalRepresentative_reversedPiece_fine
    (hmin : IsMinimalRepresentative B C x)
    (hx : ConjugatesLevi (F := F) (B.flatten S) C x) :
    IsMinimalRepresentative (B.flatten (reverseRefinement B S)) C.reverse
      (reversedPiecePermutation B S C x) := by
  have hb := isMinimalRepresentative_innerReverse B S
  have hbinv : IsMinimalRepresentative (B.flatten S)
      (B.flatten (reverseRefinement B S)) (innerReversePermutation B S)⁻¹ := by
    constructor
    · exact hb.2
    · simpa only [Equiv.Perm.inv_def, Equiv.symm_symm] using hb.1
  have hbconj := conjugatesLevi_innerReverse B S F
  have hprod : IsMinimalRepresentative (B.flatten (reverseRefinement B S)) C
      (x * innerReversePermutation B S) := by
    simpa only [inv_inv] using
      isMinimalRepresentative_mul_inv
        (isMinimalRepresentative_flatten_source B S hmin) hbinv
        (fun a b h => (blockIndex_eq_iff_of_conjugatesLevi
          (conjugatesLevi_inv hbconj) a b).mp h)
        (fun a b h => (blockIndex_eq_iff_of_conjugatesLevi hx a b).mp h)
  exact isMinimalRepresentative_reverse_inv_mul hprod
    (conjugatesLevi_mul hbconj hx)

/-- For a minimal coarse permutation with whole fine-Levi conjugacy,
target block labels increase with the source inner block labels. -/
theorem targetLabel_le_of_innerLabel_le
    (hmin : IsMinimalRepresentative B C x)
    (hx : ConjugatesLevi (F := F) (B.flatten S) C x)
    (i : Fin B.length) {a b : Fin (B.size i)}
    (hab : blockIndex (S i) a ≤ blockIndex (S i) b) :
    blockIndex C (x (B.index i a)) ≤ blockIndex C (x (B.index i b)) := by
  rcases eq_or_lt_of_le hab with heq | hlt
  · exact le_of_eq ((blockIndex_eq_iff_of_conjugatesLevi hx _ _).mpr
      ((blockIndex_flatten_index_eq_iff B S i a b).mpr heq))
  · have hab' : a < b := by
      by_contra h
      exact (not_le_of_gt hlt) (blockIndex_monotone (S i) (le_of_not_gt h))
    exact blockIndex_monotone C ((hmin.1 i) hab').le

/-- Inner and outer reversal together preserve the actual coarse minimality
needed to index the upper geometric filtration. -/
theorem isMinimalRepresentative_reversedPiece
    (hmin : IsMinimalRepresentative B C x)
    (hx : ConjugatesLevi (F := F) (B.flatten S) C x) :
    IsMinimalRepresentative B C.reverse (reversedPiecePermutation B S C x) := by
  have hfine := isMinimalRepresentative_reversedPiece_fine B S hmin hx
  have hlabel : ∀ i, Monotone (fun a : Fin (B.size i) =>
      blockIndex C.reverse (reversedPiecePermutation B S C x (B.index i a))) := by
    intro i a b hab
    simp only [reversedPiecePermutation, Equiv.Perm.mul_apply, Equiv.Perm.inv_def,
      innerReversePermutation, blockPermOf_index, blockIndex_reversePermutation_symm]
    apply Fin.rev_le_rev.mpr
    apply targetLabel_le_of_innerLabel_le B S hmin hx i
    rw [blockIndex_reversePermutation, blockIndex_reversePermutation]
    exact Fin.rev_le_rev.mpr (blockIndex_monotone (S i).reverse hab)
  exact ⟨fun i a b hab => lt_of_blockIndex_le C.reverse hfine.2
    (index_strictMono B i hab) (hlabel i hab.le), hfine.2⟩

/-- The concrete minimal index of the reversed whole piece in the upper
geometric filtration. -/
def reversedPieceMinimalRepresentative
    (hmin : IsMinimalRepresentative B C x)
    (hx : ConjugatesLevi (F := F) (B.flatten S) C x) :
    MinimalRepresentatives B C.reverse :=
  ⟨reversedPiecePermutation B S C x,
    isMinimalRepresentative_reversedPiece B S hmin hx⟩

end Langlands.Geometric.RefinedOppositePieceTransport
