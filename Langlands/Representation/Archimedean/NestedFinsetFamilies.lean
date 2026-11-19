import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Uniqueness of a nested family from its sizes and occurrence counts -/

set_option autoImplicit false

namespace Langlands.Archimedean

open Finset

private theorem sum_card_inter_eq_sum_card_filter {ι α : Type*} [Fintype ι] [DecidableEq α]
    (q : ι → Finset α) (s : Finset α) :
    (∑ j, (q j ∩ s).card) = ∑ a ∈ s, (univ.filter fun j => a ∈ q j).card := by
  simp only [inter_comm _ s, ← filter_mem_eq_inter, card_eq_sum_ones, sum_filter]
  exact sum_comm

/-- If the target sets are nested, the cardinalities of the sets and the occurrence count of
each element determine the entire family. -/
theorem eq_antitone_of_card_of_occurrences {ι α : Type*} [LinearOrder ι] [Fintype ι]
    [DecidableEq α] (q target : ι → Finset α) (hnested : Antitone target)
    (hcard : ∀ i, (q i).card = (target i).card)
    (hoccurs : ∀ a, (univ.filter fun i => a ∈ q i).card =
      (univ.filter fun i => a ∈ target i).card) :
    q = target := by
  funext i
  have hle (j : ι) : (q j ∩ target i).card ≤ (target j ∩ target i).card := by
    rcases le_total i j with hij | hji
    · rw [inter_eq_left.mpr (hnested hij), ← hcard j]
      exact card_le_card inter_subset_left
    · rw [inter_eq_right.mpr (hnested hji)]
      exact card_le_card inter_subset_right
  have hsum : (∑ j, (q j ∩ target i).card) = ∑ j, (target j ∩ target i).card := by
    rw [sum_card_inter_eq_sum_card_filter, sum_card_inter_eq_sum_card_filter]
    exact sum_congr rfl fun a _ => hoccurs a
  have heq : (q i ∩ target i).card = (target i ∩ target i).card := by
    refine le_antisymm (hle i) ?_
    by_contra! hlt
    exact (not_lt_of_ge hsum.ge) (sum_lt_sum (fun j _ => hle j) ⟨i, mem_univ i, hlt⟩)
  have hsubset : target i ⊆ q i := by
    rw [inter_self] at heq
    have h : q i ∩ target i = target i := eq_of_subset_of_card_le inter_subset_right heq.ge
    exact h ▸ inter_subset_left
  exact (eq_of_subset_of_card_le hsubset (hcard i).le).symm

end Langlands.Archimedean
