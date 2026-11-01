import Langlands.Representation.Exponents.ReversedCoarseProjectionWeylRigidityStatement
import Langlands.Representation.Geometric.RefinedOppositePieceMinimal
import Langlands.Representation.Exponents.SupportedRegularWeylConeNumerics
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof

/-! Coarse projection rigidity in raw reversed upper-geometric indexing. -/

namespace Langlands.Exponents

open GeneralLinear Geometric Finset
open scoped BigOperators

theorem reversedCoarseProjectionWeylRigidity :
    ReversedCoarseProjectionWeylRigidityStatement := by
  intro n B t v x ht hv hx hproj
  let w : Equiv.Perm (Fin n) := B.reversePermutation * v
  let A : Fin n → ℝ := fun a => t (blockIndex B a)
  have hpair : (∑ a, x a * A (w a)) ≤ 0 := by
    rw [← B.indexEquiv.sum_comp, Fintype.sum_sigma]
    apply Finset.sum_nonpos
    intro i _
    change (∑ a : Fin (B.size i), x (B.index i a) * A (w (B.index i a))) ≤ 0
    have hmono : Monotone (fun a : Fin (B.size i) => A (w (B.index i a))) := by
      intro a b hab
      dsimp only [A, w]
      simp only [Equiv.Perm.mul_apply,
        RefinedOppositePieceTransport.blockIndex_reversePermutation]
      exact ht.antitone (Fin.rev_le_rev.mpr
        (blockIndex_monotone B.reverse ((hv.1 i).monotone hab)))
    have hp := SupportedRegularWeylComparison.closedCone_pairing_antitone
      (hx i) (fun a => -A (w (B.index i a))) (fun a b hab => neg_le_neg (hmono hab))
    simpa only [mul_neg, Finset.sum_neg_distrib, neg_nonneg] using hp
  have hpair' : (∑ a, x (w.symm a) * A a) ≤ 0 := by
    rw [← Equiv.sum_comp w (fun a => x (w.symm a) * A a)]
    simpa only [Equiv.symm_apply_apply] using hpair
  have hproj0 (i : Fin B.length) :
      (∑ a : Fin (B.size i),
        (x (w.symm (B.index i a)) + A (w.symm (B.index i a)) -
          A (B.index i a))) = 0 := by
    simp only [Finset.sum_sub_distrib, A, blockIndex_index]
    rw [hproj]
    simp
  have hprojpair :
      (∑ a, (x (w.symm a) + A (w.symm a) - A a) * A a) = 0 := by
    rw [← B.indexEquiv.sum_comp, Fintype.sum_sigma]
    apply Finset.sum_eq_zero
    intro i _
    change (∑ a : Fin (B.size i),
      (x (w.symm (B.index i a)) + A (w.symm (B.index i a)) -
        A (B.index i a)) * t (blockIndex B (B.index i a))) = 0
    simp_rw [blockIndex_index, ← Finset.sum_mul, hproj0, zero_mul]
  have hbalance : (∑ a, A a * (A a - A (w.symm a))) ≤ 0 := by
    have heq :
        (∑ a, (x (w.symm a) + A (w.symm a) - A a) * A a) =
          (∑ a, x (w.symm a) * A a) -
            (∑ a, A a * (A a - A (w.symm a))) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro a _
      ring
    rw [heq] at hprojpair
    linarith
  have hnorm : (∑ a, A (w.symm a) ^ 2) = ∑ a, A a ^ 2 :=
    Equiv.sum_comp w.symm (fun a => A a ^ 2)
  have henergy :
      (∑ a, (A a - A (w.symm a)) ^ 2) =
        2 * ∑ a, A a * (A a - A (w.symm a)) := by
    calc
      _ = ∑ a, (A a ^ 2 + A (w.symm a) ^ 2 -
          2 * (A a * A (w.symm a))) := by
        apply Finset.sum_congr rfl
        intro a _
        ring
      _ = (∑ a, A a ^ 2) + (∑ a, A (w.symm a) ^ 2) -
          2 * (∑ a, A a * A (w.symm a)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.mul_sum]
      _ = _ := by
        rw [hnorm]
        simp_rw [mul_sub]
        rw [Finset.sum_sub_distrib]
        simp_rw [← sq]
        ring
  have hzero : (∑ a, (A a - A (w.symm a)) ^ 2) = 0 := by
    apply le_antisymm
    · rw [henergy]
      linarith
    · exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hA (a : Fin n) : A a = A (w.symm a) := by
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => sq_nonneg (A a - A (w.symm a)))).mp hzero a (mem_univ a)
    nlinarith only [hz]
  have hblock : w ∈ blockWeyl B := by
    intro a
    apply ht.injective
    simpa only [A, Equiv.symm_apply_apply] using hA (w a)
  have hrev : IsMinimalRepresentative B B.reverse B.reversePermutation.symm := by
    constructor
    · exact OppositeCuspidalJacquetFiltration.reversePermutation_symm_index_strictMono B
    · intro i a b hab
      change B.reversePermutation (B.reverse.index i a) <
        B.reversePermutation (B.reverse.index i b)
      erw [B.reversePermutation_index i a, B.reversePermutation_index i b]
      exact index_strictMono B i.rev hab
  have hcoset : weylDoubleCoset B B.reverse ⟨v, hv⟩ =
      weylDoubleCoset B B.reverse ⟨B.reversePermutation.symm, hrev⟩ := by
    apply DoubleCoset.eq.mpr
    refine ⟨1, (blockWeyl B.reverse).one_mem, w⁻¹, (blockWeyl B).inv_mem hblock, ?_⟩
    dsimp only [w]
    rw [← Equiv.Perm.inv_def]
    group
  exact congrArg Subtype.val (weylDoubleCoset_injective B B.reverse hcoset)

end Langlands.Exponents
