import Langlands.Representation.Aubert.TwoSidedSupport
import Mathlib.Data.List.NodupEquivFin

/-! Generic rank-ordered support chains and their two-sided modified supports. -/

noncomputable section

namespace Langlands.Aubert.Support

universe u

section Rank

variable {W : Type u} (rank : W → ℕ)

/-- Aubert's class `Θ`: a support containing every element of strictly larger
rank than one of its members. -/
def IsRankUpper (θ : Set W) : Prop :=
  ∀ w ∈ θ, ∀ v : W, rank w < rank v → v ∈ θ

variable [Fintype W]

/-- An exhaustive list of the elements in decreasing rank. Elements of equal rank
retain any order supplied by the finite enumeration. -/
def rankOrderedList : List W :=
  (Finset.univ.toList).mergeSort (fun v w => decide (rank w ≤ rank v))

theorem rankOrderedList_nodup : (rankOrderedList rank).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr (Finset.nodup_toList _)

@[simp] theorem mem_rankOrderedList (w : W) : w ∈ rankOrderedList rank :=
  (List.mergeSort_perm _ _).mem_iff.mpr (Finset.mem_toList.mpr (Finset.mem_univ w))

theorem rankOrderedList_length : (rankOrderedList rank).length = Fintype.card W := by
  rw [rankOrderedList, List.length_mergeSort, Finset.length_toList, Finset.card_univ]

theorem rankOrderedList_pairwise :
    (rankOrderedList rank).Pairwise (fun v w => rank w ≤ rank v) := by
  simpa only [rankOrderedList, decide_eq_true_eq] using
    List.pairwise_mergeSort
      (le := fun v w : W => decide (rank w ≤ rank v))
      (fun a b c hab hbc => by simpa only [decide_eq_true_eq] using
        (le_trans (of_decide_eq_true hbc) (of_decide_eq_true hab)))
      (fun a b => by simp only [Bool.or_eq_true, decide_eq_true_eq]; omega)
      (Finset.univ.toList)

variable [DecidableEq W]

/-- The position in the rank-ordered list bijectively enumerates all elements. -/
def rankOrderedEquiv : Fin (rankOrderedList rank).length ≃ W :=
  List.Nodup.getEquivOfForallMemList (rankOrderedList rank)
    (rankOrderedList_nodup rank) (mem_rankOrderedList rank)

theorem rankOrderedEquiv_antitone :
    Antitone (fun i => rank (rankOrderedEquiv rank i)) := by
  intro i j hij
  rcases eq_or_lt_of_le hij with heq | hlt
  · exact heq ▸ le_rfl
  · exact (rankOrderedList_pairwise rank).rel_get_of_lt hlt

/-- The first `i` elements of the decreasing-rank enumeration. Indices beyond its
finite length give the full support. -/
def rankOrderedSupport (i : ℕ) : Set W :=
  {w | ((rankOrderedEquiv rank).symm w).val < i}

@[simp] theorem mem_rankOrderedSupport (i : ℕ) (w : W) :
    w ∈ rankOrderedSupport rank i ↔ ((rankOrderedEquiv rank).symm w).val < i :=
  Iff.rfl

theorem rankOrderedSupport_monotone : Monotone (rankOrderedSupport rank) := by
  intro i j hij w hw
  exact lt_of_lt_of_le hw hij

@[simp] theorem rankOrderedSupport_zero : rankOrderedSupport rank 0 = ∅ := by
  ext w
  simp

theorem rankOrderedSupport_of_length_le {i : ℕ} (hi : (rankOrderedList rank).length ≤ i) :
    rankOrderedSupport rank i = Set.univ := by
  ext w
  exact iff_of_true (lt_of_lt_of_le ((rankOrderedEquiv rank).symm w).isLt hi)
    (Set.mem_univ w)

@[simp] theorem rankOrderedSupport_length :
    rankOrderedSupport rank (rankOrderedList rank).length = Set.univ :=
  rankOrderedSupport_of_length_le rank le_rfl

/-- The element added at step `i` of the decreasing-rank enumeration. -/
abbrev rankOrderedElement (i : ℕ) (hi : i < (rankOrderedList rank).length) : W :=
  rankOrderedEquiv rank ⟨i, hi⟩

/-- Each step adds exactly the element at its new index. -/
theorem rankOrderedSupport_step (i : ℕ) (hi : i < (rankOrderedList rank).length) :
    rankOrderedSupport rank i =
      rankOrderedSupport rank (i + 1) \ {rankOrderedElement rank i hi} := by
  ext w
  have heq : w = rankOrderedElement rank i hi ↔
      ((rankOrderedEquiv rank).symm w).val = i := by
    constructor
    · intro h
      simp [h]
    · intro h
      apply (rankOrderedEquiv rank).symm.injective
      simpa only [Equiv.symm_apply_apply, Fin.ext_iff] using h
  simp only [Set.mem_sdiff, mem_rankOrderedSupport, Set.mem_singleton_iff, heq]
  omega

theorem rankOrderedElement_mem_succ (i : ℕ) (hi : i < (rankOrderedList rank).length) :
    rankOrderedElement rank i hi ∈ rankOrderedSupport rank (i + 1) := by
  simp

theorem rankOrderedElement_not_mem (i : ℕ) (hi : i < (rankOrderedList rank).length) :
    rankOrderedElement rank i hi ∉ rankOrderedSupport rank i := by
  simp

/-- Every prefix lies in Aubert's class `Θ`. -/
theorem rankOrderedSupport_isRankUpper (i : ℕ) :
    IsRankUpper rank (rankOrderedSupport rank i) := by
  intro v hv z hz
  by_contra hnot
  have hidx : (rankOrderedEquiv rank).symm v ≤ (rankOrderedEquiv rank).symm z := by
    change ((rankOrderedEquiv rank).symm v).val ≤ ((rankOrderedEquiv rank).symm z).val
    simp only [mem_rankOrderedSupport] at hv hnot
    omega
  have hlen := rankOrderedEquiv_antitone rank hidx
  simp only [Equiv.apply_symm_apply] at hlen
  omega

/-- The newly added element has minimum rank in the enlarged prefix: the elements
remaining after its removal have rank at least its rank. -/
theorem rankOrderedElement_rank_le (i : ℕ) (hi : i < (rankOrderedList rank).length)
    (v : W) (hv : v ∈ rankOrderedSupport rank (i + 1)) :
    rank (rankOrderedElement rank i hi) ≤ rank v := by
  have hidx : (rankOrderedEquiv rank).symm v ≤ ⟨i, hi⟩ := by
    change ((rankOrderedEquiv rank).symm v).val ≤ i
    exact Nat.le_of_lt_succ hv
  simpa only [Equiv.apply_symm_apply] using rankOrderedEquiv_antitone rank hidx

end Rank

section TwoSided

variable {W : Type u} [Group W] [Fintype W] [DecidableEq W]
variable (H K : Subgroup W) (rank : W → ℕ)

/-- The modified support `θ_i'` of Ban–Jantzen: the largest subset of the `i`-th
prefix which is left `H`-invariant and right `K`-invariant. -/
def modifiedRankSupport (i : ℕ) : Set W :=
  twoSidedCore H K (rankOrderedSupport rank i)

theorem modifiedRankSupport_subset (i : ℕ) :
    modifiedRankSupport H K rank i ⊆ rankOrderedSupport rank i :=
  twoSidedCore_subset H K _

theorem modifiedRankSupport_invariant (i : ℕ) :
    IsTwoSidedInvariant H K (modifiedRankSupport H K rank i) :=
  twoSidedCore_invariant H K _

theorem modifiedRankSupport_monotone : Monotone (modifiedRankSupport H K rank) :=
  fun _ _ hij => twoSidedCore_mono H K (rankOrderedSupport_monotone rank hij)

@[simp] theorem modifiedRankSupport_zero : modifiedRankSupport H K rank 0 = ∅ := by
  simp [modifiedRankSupport]

@[simp] theorem modifiedRankSupport_length :
    modifiedRankSupport H K rank (rankOrderedList rank).length = Set.univ := by
  simp [modifiedRankSupport]

/-- Consecutive modified supports: the smaller one is the larger one with the
entire double coset of the newly added element removed. -/
theorem modifiedRankSupport_step (i : ℕ) (hi : i < (rankOrderedList rank).length) :
    modifiedRankSupport H K rank i =
      modifiedRankSupport H K rank (i + 1) \
        DoubleCoset.doubleCoset (rankOrderedElement rank i hi) H K := by
  rw [modifiedRankSupport, rankOrderedSupport_step rank i hi, twoSidedCore_diff_singleton]
  rfl

/-- Consecutive modified supports differ exactly when the newly added element lies
in the larger one. -/
theorem modifiedRankSupport_succ_ne_iff (i : ℕ) (hi : i < (rankOrderedList rank).length) :
    modifiedRankSupport H K rank (i + 1) ≠ modifiedRankSupport H K rank i ↔
      rankOrderedElement rank i hi ∈ modifiedRankSupport H K rank (i + 1) := by
  rw [modifiedRankSupport, modifiedRankSupport, rankOrderedSupport_step rank i hi]
  exact twoSidedCore_diff_singleton_ne_iff H K _ _

/-- In a changing step the difference of consecutive modified supports is the
whole double coset of the newly added element. -/
theorem modifiedRankSupport_succ_diff (i : ℕ) (hi : i < (rankOrderedList rank).length)
    (hw : rankOrderedElement rank i hi ∈ modifiedRankSupport H K rank (i + 1)) :
    modifiedRankSupport H K rank (i + 1) \ modifiedRankSupport H K rank i =
      DoubleCoset.doubleCoset (rankOrderedElement rank i hi) H K := by
  rw [modifiedRankSupport, modifiedRankSupport, rankOrderedSupport_step rank i hi]
  exact twoSidedCore_singleton_step H K _ _ hw

/-- Double-coset minimality from the rank filtration: if consecutive modified
supports differ, the newly added element has minimum rank on its entire double
coset. -/
theorem modifiedRankSupport_succ_minimal (i : ℕ) (hi : i < (rankOrderedList rank).length)
    (hne : modifiedRankSupport H K rank (i + 1) ≠ modifiedRankSupport H K rank i) :
    ∀ v ∈ DoubleCoset.doubleCoset (rankOrderedElement rank i hi) H K,
      rank (rankOrderedElement rank i hi) ≤ rank v := by
  apply singleton_drop_forces_minimal H K rank (rankOrderedSupport rank (i + 1))
  · exact fun v hv => rankOrderedElement_rank_le rank i hi v hv.1
  · rw [← rankOrderedSupport_step rank i hi]
    exact hne

/-- Consecutive modified supports agree when the newly added element is not in
the larger one. -/
theorem modifiedRankSupport_succ_eq (i : ℕ) (hi : i < (rankOrderedList rank).length)
    (hw : rankOrderedElement rank i hi ∉ modifiedRankSupport H K rank (i + 1)) :
    modifiedRankSupport H K rank (i + 1) = modifiedRankSupport H K rank i := by
  by_contra hne
  exact hw ((modifiedRankSupport_succ_ne_iff H K rank i hi).mp hne)

end TwoSided

end Langlands.Aubert.Support
