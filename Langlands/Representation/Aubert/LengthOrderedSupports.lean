import Langlands.Representation.Aubert.LengthMinimality
import Mathlib.Data.List.NodupEquivFin

/-! A finite increasing support chain ordered by decreasing inversion length. -/

noncomputable section

namespace Langlands.Aubert.Support

variable {n : ℕ}

/-- An exhaustive list of actual Weyl permutations in decreasing inversion length.
Permutations of the same length retain any order supplied by the finite enumeration. -/
def lengthOrderedWeylList (n : ℕ) : List (Equiv.Perm (Fin n)) :=
  (Finset.univ.toList).mergeSort (fun v w => decide (inversionLength w ≤ inversionLength v))

theorem lengthOrderedWeylList_nodup (n : ℕ) : (lengthOrderedWeylList n).Nodup := by
  classical
  exact (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

@[simp] theorem mem_lengthOrderedWeylList (w : Equiv.Perm (Fin n)) :
    w ∈ lengthOrderedWeylList n := by
  classical
  exact (List.mergeSort_perm _ _).mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ w))

theorem lengthOrderedWeylList_pairwise (n : ℕ) :
    (lengthOrderedWeylList n).Pairwise
      (fun v w => inversionLength w ≤ inversionLength v) := by
  classical
  simpa only [lengthOrderedWeylList, decide_eq_true_eq] using
    List.pairwise_mergeSort
      (le := fun v w : Equiv.Perm (Fin n) => decide (inversionLength w ≤ inversionLength v))
      (fun a b c hab hbc => by simpa only [decide_eq_true_eq] using
        (le_trans (of_decide_eq_true hbc) (of_decide_eq_true hab)))
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      (Finset.univ.toList)

/-- The position in the length-ordered list bijectively enumerates all Weyl elements. -/
def lengthOrderedWeylEquiv (n : ℕ) :
    Fin (lengthOrderedWeylList n).length ≃ Equiv.Perm (Fin n) := by
  classical
  exact List.Nodup.getEquivOfForallMemList (lengthOrderedWeylList n)
    (lengthOrderedWeylList_nodup n) mem_lengthOrderedWeylList

theorem lengthOrderedWeylEquiv_antitone (n : ℕ) :
    Antitone (fun i => inversionLength (lengthOrderedWeylEquiv n i)) := by
  intro i j hij
  rcases eq_or_lt_of_le hij with heq | hlt
  · exact heq ▸ le_rfl
  · exact (lengthOrderedWeylList_pairwise n).rel_get_of_lt hlt

/-- The first `i` elements of the decreasing-length enumeration. Indices beyond
its finite length give the full support. -/
def lengthOrderedSupport (n i : ℕ) : Set (Equiv.Perm (Fin n)) :=
  {w | ((lengthOrderedWeylEquiv n).symm w).val < i}

@[simp] theorem mem_lengthOrderedSupport (i : ℕ) (w : Equiv.Perm (Fin n)) :
    w ∈ lengthOrderedSupport n i ↔ ((lengthOrderedWeylEquiv n).symm w).val < i := Iff.rfl

theorem lengthOrderedSupport_monotone (n : ℕ) : Monotone (lengthOrderedSupport n) := by
  intro i j hij w hw
  exact lt_of_lt_of_le hw hij

@[simp] theorem lengthOrderedSupport_zero (n : ℕ) : lengthOrderedSupport n 0 = ∅ := by
  ext w
  simp

@[simp] theorem lengthOrderedSupport_top (n : ℕ) :
    lengthOrderedSupport n (lengthOrderedWeylList n).length = Set.univ := by
  ext w
  exact iff_of_true ((lengthOrderedWeylEquiv n).symm w).isLt (Set.mem_univ w)

/-- Each step adds exactly the permutation at its new index. -/
theorem lengthOrderedSupport_step (i : ℕ) (hi : i < (lengthOrderedWeylList n).length) :
    lengthOrderedSupport n i = lengthOrderedSupport n (i + 1) \
      {lengthOrderedWeylEquiv n ⟨i, hi⟩} := by
  ext w
  have heq : w = lengthOrderedWeylEquiv n ⟨i, hi⟩ ↔
      ((lengthOrderedWeylEquiv n).symm w).val = i := by
    constructor
    · intro h
      simp [h]
    · intro h
      apply (lengthOrderedWeylEquiv n).symm.injective
      simpa only [Equiv.symm_apply_apply, Fin.ext_iff] using h
  simp only [Set.mem_sdiff, mem_lengthOrderedSupport, Set.mem_singleton_iff, heq]
  omega

@[simp] theorem lengthOrderedWeylEquiv_mem_succ (i : ℕ)
    (hi : i < (lengthOrderedWeylList n).length) :
    lengthOrderedWeylEquiv n ⟨i, hi⟩ ∈ lengthOrderedSupport n (i + 1) := by
  simp

/-- Every prefix is upward closed for strict inversion-length inequalities. -/
theorem lengthOrderedSupport_upper (i : ℕ) (v : Equiv.Perm (Fin n))
    (hv : v ∈ lengthOrderedSupport n i) (z : Equiv.Perm (Fin n))
    (hz : inversionLength v < inversionLength z) : z ∈ lengthOrderedSupport n i := by
  by_contra hnot
  have hidx : (lengthOrderedWeylEquiv n).symm v ≤ (lengthOrderedWeylEquiv n).symm z := by
    change ((lengthOrderedWeylEquiv n).symm v).val ≤ ((lengthOrderedWeylEquiv n).symm z).val
    simp only [mem_lengthOrderedSupport] at hv hnot
    omega
  have hlen := lengthOrderedWeylEquiv_antitone n hidx
  simp only [Equiv.apply_symm_apply] at hlen
  omega

/-- The newly added element has minimum length among the enlarged prefix. -/
theorem lengthOrderedSupport_step_minimum (i : ℕ)
    (hi : i < (lengthOrderedWeylList n).length) (v : Equiv.Perm (Fin n))
    (hv : v ∈ lengthOrderedSupport n (i + 1)) :
    inversionLength (lengthOrderedWeylEquiv n ⟨i, hi⟩) ≤ inversionLength v := by
  have hidx : (lengthOrderedWeylEquiv n).symm v ≤ ⟨i, hi⟩ := by
    change ((lengthOrderedWeylEquiv n).symm v).val ≤ i
    exact Nat.le_of_lt_succ hv
  simpa only [Equiv.apply_symm_apply] using lengthOrderedWeylEquiv_antitone n hidx

end Langlands.Aubert.Support
