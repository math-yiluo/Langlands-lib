import Langlands.Representation.Geometric.PointwiseJacquetCoefficientStatement
import Langlands.Representation.Geometric.TypeASolomonCoefficientProof

/-! Fixed-permutation cancellation, transported to the actual target coordinates. -/

namespace Langlands.Geometric

open GeneralLinear

variable {n : ℕ}

namespace TypeASolomon

/-- The sorting permutation lists the original blocks in reverse order. -/
theorem reversal_eq_reversePermutation_symm (B : BlockShape n) :
    reversal B = B.reversePermutation.symm := by
  have hs : B.reversePermutation = Tuple.sort (reversalKey B) := by
    rw [Tuple.eq_sort_iff]
    refine ⟨?_, fun i j hij heq => ?_⟩
    · intro x y hxy
      obtain ⟨⟨i, a⟩, rfl⟩ := B.reverse.indexEquiv.surjective x
      obtain ⟨⟨j, b⟩, rfl⟩ := B.reverse.indexEquiv.surjective y
      change B.reverse.index i a ≤ B.reverse.index j b at hxy
      have hij := blockIndex_monotone B.reverse hxy
      rw [blockIndex_index, blockIndex_index] at hij
      change Fin B.length at i j
      change Fin (B.size i.rev) at a
      change Fin (B.size j.rev) at b
      change reversalKey B (B.reversePermutation (B.reverse.index i a)) ≤
        reversalKey B (B.reversePermutation (B.reverse.index j b))
      have ha := B.reversePermutation_index (i : Fin B.length) a
      have hb := B.reversePermutation_index (j : Fin B.length) b
      rw [ha, hb]
      rcases hij.lt_or_eq with hij | rfl
      · apply le_of_lt
        rw [reversalKey_lt_iff, blockIndex_index, blockIndex_index]
        exact Or.inl (Fin.rev_lt_rev.mpr hij)
      · have hab := (index_strictMono B.reverse i).le_iff_le.mp hxy
        rcases hab.lt_or_eq with hab | rfl
        · apply le_of_lt
          rw [reversalKey_lt_iff, blockIndex_index, blockIndex_index]
          exact Or.inr ⟨rfl, index_strictMono B i.rev hab⟩
        · exact le_rfl
    · exact absurd (B.reversePermutation.injective (reversalKey_injective B heq)) hij.ne
  rw [reversal, ← hs]

open Classical in
/-- Each fixed permutation has zero signed cut coefficient except at the reversal. -/
theorem sum_admissible_eq_ite (B K : BlockShape n) (hKB : B.cuts ⊆ K.cuts)
    (w : Equiv.Perm (Fin n)) :
    (∑ S : Finset (Fin (n - 1)),
      if Admissible B K w S then (-1 : ℤ) ^ Sᶜ.card else 0) =
        if w = reversal B then (-1 : ℤ) ^ K.uncuts.card else 0 := by
  by_cases hw : w = reversal B
  · rw [hw, ite_eq_left rfl]
    exact sum_reversal B K hKB
  · rw [ite_eq_right hw]
    by_cases hB : SourceIncreasing B w
    · have hfree : ∃ e₀ : Fin (n - 1), e₀ ∉ permutationDescents w.symm ∧
          ∀ i : Fin (n - 1), i ∉ B.cuts → e₀.val = (w (edgeLo i)).val →
            e₀.val + 1 ≠ (w (edgeHi i)).val := by
        by_contra hno
        push Not at hno
        exact hw (eq_reversal B hB hno)
      obtain ⟨e₀, hD, hP⟩ := hfree
      exact sum_eq_zero_of_free B K w e₀ hD hP
    · exact Finset.sum_eq_zero fun S _ => ite_eq_right fun h => hB h.1

end TypeASolomon

open TypeASolomon in
open Classical in
/-- Pointwise cancellation with the actual target intersection and block reversal. -/
theorem pointwiseJacquetCoefficientStatement : PointwiseJacquetCoefficientStatement := by
  intro n B K w
  let _ : Fintype (BlockShape n) := Fintype.ofFinite (BlockShape n)
  intro hKB
  have hcuts := (blockWeyl_le_iff_cuts_subset B K).mp hKB
  calc (∑ C : BlockShape n,
      if IsMinimalRepresentative C B w ∧
        blockWeyl B ⊓ (blockWeyl C).comap (MulAut.conj w⁻¹).toMonoidHom = blockWeyl K
      then (-1 : ℤ) ^ (n - C.length) else 0)
      = ∑ C : BlockShape n,
          if Admissible B K w.symm C.cuts then (-1 : ℤ) ^ C.cutsᶜ.card else 0 := by
        refine Finset.sum_congr rfl fun C _ => ?_
        have hminimal : IsMinimalRepresentative C B w ↔
            IsMinimalRepresentative B C w.symm := by
          simp only [IsMinimalRepresentative, Equiv.symm_symm]
          exact and_comm
        simp only [Equiv.Perm.inv_def, hminimal, admissible_iff B C K hcuts w.symm,
          C.sign_eq_pow_uncuts_card, BlockShape.uncuts, ← Finset.compl_eq_univ_sdiff]
    _ = ∑ S : Finset (Fin (n - 1)),
          if Admissible B K w.symm S then (-1 : ℤ) ^ Sᶜ.card else 0 :=
        Fintype.sum_equiv (BlockShape.cutEquiv n) _ _ fun C => rfl
    _ = if w.symm = reversal B then (-1 : ℤ) ^ K.uncuts.card else 0 :=
        sum_admissible_eq_ite B K hcuts w.symm
    _ = if w = B.reversePermutation then (-1 : ℤ) ^ (n - K.length) else 0 := by
        have heq : w.symm = B.reversePermutation.symm ↔ w = B.reversePermutation := by
          constructor
          · intro h
            simpa only [Equiv.symm_symm] using congrArg Equiv.symm h
          · exact congrArg Equiv.symm
        simp only [reversal_eq_reversePermutation_symm, heq, K.uncuts_card]

end Langlands.Geometric
