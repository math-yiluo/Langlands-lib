import Langlands.Representation.Whittaker.NonOpenCharacterStatement
import Langlands.Representation.Geometric.WeylMinimalRepresentativeProof
import Mathlib.LinearAlgebra.Matrix.ElementaryRowOperations

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear Geometric
open scoped BigOperators

universe uK

private theorem reverse_block_labels {d : ℕ} (B : BlockShape d) (x : Fin d) :
    blockIndex B (B.reversePermutation x) = (blockIndex B.reverse x).rev := by
  obtain ⟨⟨i, a⟩, rfl⟩ := B.reverse.indexEquiv.surjective x
  change Fin B.length at i
  change Fin (B.size i.rev) at a
  change blockIndex B (B.reversePermutation (B.reverse.index i a)) =
    (blockIndex B.reverse (B.reverse.index i a)).rev
  exact (congrArg (blockIndex B) (B.reversePermutation_index i a)).trans
    ((blockIndex_index B i.rev a).trans
      (congrArg (fun j : Fin B.length => j.rev) (blockIndex_index B.reverse i a).symm))

private theorem eq_reverse_of_antitone {d : ℕ} (B : BlockShape d)
    (v : Equiv.Perm (Fin d))
    (hv : ∀ i, StrictMono (fun a : Fin (B.size i) => v (B.index i a)))
    (hf : Antitone (fun x => blockIndex B (v.symm x))) :
    v = B.reversePermutation.symm := by
  have hr : Antitone (fun x => blockIndex B (B.reversePermutation x)) := by
    intro a b hab
    dsimp only
    rw [reverse_block_labels, reverse_block_labels]
    exact Fin.rev_le_rev.mpr (blockIndex_monotone B.reverse hab)
  have hlabels (x : Fin d) :
      blockIndex B (v.symm x) = blockIndex B (B.reversePermutation x) :=
    congrFun (Tuple.unique_antitone (f := blockIndex B)
      (σ := v.symm) (τ := B.reversePermutation) hf hr) x
  have hrange (i : Fin B.length) :
      Set.range (fun a => v (B.index i a)) =
        Set.range (fun a => B.reversePermutation.symm (B.index i a)) := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      have hx : blockIndex B (B.reversePermutation (v (B.index i a))) = i := by
        rw [← hlabels, Equiv.symm_apply_apply, blockIndex_index]
      obtain ⟨b, hb⟩ := exists_index_of_blockIndex_eq B hx
      exact ⟨b, by simp only [hb, Equiv.symm_apply_apply]⟩
    · rintro ⟨a, rfl⟩
      have hx : blockIndex B
          (v.symm (B.reversePermutation.symm (B.index i a))) = i := by
        rw [hlabels, Equiv.apply_symm_apply, blockIndex_index]
      obtain ⟨b, hb⟩ := exists_index_of_blockIndex_eq B hx
      exact ⟨b, by simp only [hb, Equiv.apply_symm_apply]⟩
  have hstrict (i : Fin B.length) :
      StrictMono (fun a : Fin (B.size i) => B.reversePermutation.symm (B.index i a)) := by
    obtain ⟨i, rfl⟩ := Fin.rev_surjective i
    intro a b hab
    simp only [B.reversePermutation_symm_index]
    exact index_strictMono B.reverse i hab
  apply Equiv.ext
  intro x
  obtain ⟨⟨i, a⟩, rfl⟩ := B.indexEquiv.surjective x
  exact congrFun ((hv i).eq_of_range_eq (hstrict i) (hrange i)) a

private theorem exists_adjacent_block_increase {n : ℕ} (B : BlockShape (n + 1))
    (v : MinimalRepresentatives B (BlockShape.singletons (n + 1)))
    (hne : v.val ≠ B.reversePermutation.symm) :
    ∃ i : Fin n,
      blockIndex B (v.val.symm i.castSucc) < blockIndex B (v.val.symm i.succ) := by
  by_contra h
  apply hne
  apply eq_reverse_of_antitone B v.val v.property.1
  apply Fin.antitone_iff_succ_le.mpr
  intro i
  exact le_of_not_gt (fun hi => h ⟨i, hi⟩)

private def adjacentRoot {n : ℕ} (K : Type uK) [Field K] (i : Fin n) (t : K) :
    upperUnipotent (n + 1) K :=
  ⟨Matrix.GeneralLinearGroup.transvection i.castSucc i.succ
    (ne_of_lt i.castSucc_lt_succ) t, by
    constructor
    · intro a b hba
      change Matrix.transvection i.castSucc i.succ t a b = 0
      have hroot : ¬ (i.castSucc = a ∧ i.succ = b) := by
        rintro ⟨rfl, rfl⟩
        exact (not_lt_of_ge i.castSucc_lt_succ.le) hba
      have hab : a ≠ b := ne_of_gt hba
      simp [Matrix.transvection, hab, hroot]
    · intro a
      change Matrix.transvection i.castSucc i.succ t a a = 1
      have hroot : ¬ (i.castSucc = a ∧ i.succ = a) := by
        rintro ⟨ha, hb⟩
        exact (ne_of_lt i.castSucc_lt_succ) (ha.trans hb.symm)
      simp [Matrix.transvection, hroot]⟩

private theorem adjacentRoot_entry {n : ℕ} (K : Type uK) [Field K]
    (i : Fin n) (t : K) (a b : Fin (n + 1)) :
    (adjacentRoot K i t).val a b =
      (if a = b then 1 else 0) + (if i.castSucc = a ∧ i.succ = b then t else 0) := by
  change Matrix.transvection i.castSucc i.succ t a b = _
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]

private theorem inverse_permutation_conjugate_entry {d : ℕ} (K : Type uK) [Field K]
    (v : Equiv.Perm (Fin d)) (g : Langlands.GeneralLinear d K) (a b : Fin d) :
    ((permutation d K v)⁻¹ * g * permutation d K v) a b = g (v a) (v b) := by
  rw [permutation_inv, mul_permutation_entry, permutation_mul_entry]
  rfl

private theorem conjugate_root_identity_entry {n : ℕ} (K : Type uK) [Field K]
    (B : BlockShape (n + 1)) (v : Equiv.Perm (Fin (n + 1))) (i : Fin n) (t : K)
    (hi : blockIndex B (v.symm i.castSucc) < blockIndex B (v.symm i.succ))
    (a b : Fin (n + 1)) (hab : blockIndex B b ≤ blockIndex B a) :
    ((permutation (n + 1) K v)⁻¹ * (adjacentRoot K i t).val *
      permutation (n + 1) K v) a b = if a = b then 1 else 0 := by
  rw [inverse_permutation_conjugate_entry, adjacentRoot_entry]
  have hroot : ¬ (i.castSucc = v a ∧ i.succ = v b) := by
    rintro ⟨ha, hb⟩
    rw [ha, hb, Equiv.symm_apply_apply, Equiv.symm_apply_apply] at hi
    exact (not_lt_of_ge hab) hi
  simp only [hroot, ite_false, add_zero, v.injective.eq_iff]

private theorem adjacentRoot_sum {n : ℕ} (K : Type uK) [Field K]
    (i : Fin n) (t : K) :
    (∑ j : Fin n, (adjacentRoot K i t).val j.castSucc j.succ) = t := by
  classical
  rw [Finset.sum_eq_single i]
  · rw [adjacentRoot_entry]
    simp [ne_of_lt i.castSucc_lt_succ]
  · intro j _ hji
    rw [adjacentRoot_entry]
    have hne : i.castSucc ≠ j.castSucc := fun h => hji (Fin.castSucc_injective n h).symm
    simp [ne_of_lt j.castSucc_lt_succ, hne]
  · simp

/-- Every minimal representative other than the inverse block reversal has a
single radical stabilizer element detected by the ambient character. -/
theorem nonOpenCharacterWitness : NonOpenCharacterWitnessStatement := by
  classical
  intro K _ n B ψ hψ v hv
  obtain ⟨i, hi⟩ := exists_adjacent_block_increase B v hv
  obtain ⟨t, ht⟩ := AddChar.ne_one_iff.mp hψ
  let w := permutation (n + 1) K v.val
  let u := adjacentRoot K i t
  have hp : w⁻¹ * u.val * w ∈ B.parabolic K := by
    apply (B.mem_parabolic_iff K _).mpr
    intro j k a b hkj
    have hle : blockIndex B (B.index k b) ≤ blockIndex B (B.index j a) := by
      simpa only [blockIndex_index] using hkj.le
    rw [conjugate_root_identity_entry K B v.val i t hi _ _ hle]
    have hne : B.index j a ≠ B.index k b := by
      intro he
      have hh := congrArg (blockIndex B) he
      simp only [blockIndex_index] at hh
      exact (ne_of_gt hkj) hh
    simp only [hne, ite_false]
  let q : orbitStabilizer (B.parabolic K) (upperUnipotent (n + 1) K) w :=
    ⟨u, by
      change w⁻¹ * u.val * (w⁻¹)⁻¹ ∈ B.parabolic K
      simpa only [inv_inv] using hp⟩
  refine ⟨q, ?_, ?_⟩
  · change stabilizerToInducing (B.parabolic K) (upperUnipotent (n + 1) K) w q ∈
      B.unipotentRadical K
    apply (B.mem_unipotentRadical_iff K _).mpr
    intro j a b
    rw [stabilizerToInducing_apply]
    have hle : blockIndex B (B.index j b) ≤ blockIndex B (B.index j a) := by
      simp only [blockIndex_index, le_refl]
    rw [conjugate_root_identity_entry K B v.val i t hi _ _ hle]
    simp only [(B.index j).injective.eq_iff]
  · intro he
    apply ht
    have hc := congrArg (fun z : ℂˣ => (z : ℂ)) he
    change (entrywiseCharacter ψ (n + 1) u : ℂ) = 1 at hc
    rw [entrywiseCharacter_apply_sum, adjacentRoot_sum] at hc
    exact hc

end Langlands.Whittaker
