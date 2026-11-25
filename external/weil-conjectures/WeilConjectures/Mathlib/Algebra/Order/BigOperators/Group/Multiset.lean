/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Multiset
public import Mathlib.Algebra.Order.Group.Multiset
public import Mathlib.Algebra.Order.Sub.Unbundled.Basic

/-!
# Two inequalities for sums of multisets in a linearly ordered group

- `Multiset.sum_le_sum_filter_add_of_le`: a sub-multiset `T ≤ M` with one element more than the
  number of elements of `M` above `γ` has sum at most the sum of those elements plus `γ`. This
  is the bound on the weights of the constituents of an exterior power used in
  `theorem-purity-real-sheaves-curves--1`: the largest sum of `N + 1` entries of a list with exactly
  `N` entries above `γ` takes those `N` entries and one entry at most `γ`.
- `Multiset.eq_of_le_of_sum_eq`: if all elements of `s` are at most `γ` and their sum is
  `card s • γ`, all of them equal `γ`.
-/

@[expose] public section

namespace Multiset

variable {α : Type*} [AddCommGroup α] [LinearOrder α] [IsOrderedAddMonoid α]

/-- If `T ≤ M` has exactly one element more than the number of elements of `M` strictly above
`γ`, then the sum of `T` is at most the sum of the elements of `M` strictly above `γ`, plus
`γ`. -/
theorem sum_le_sum_filter_add_of_le {T M : Multiset α} (γ : α) (hT : T ≤ M)
    (hcard : card T = card (M.filter (γ < ·)) + 1) :
    T.sum ≤ (M.filter (γ < ·)).sum + γ := by
  set Mp := M.filter (γ < ·)
  set Tp := T.filter (γ < ·)
  set Tn := T.filter fun a ↦ ¬γ < a
  have hTp : Tp ≤ Mp := filter_le_filter _ hT
  have hT' : T = Tp + Tn := (filter_add_not _ T).symm
  have hMp : Mp = Tp + (Mp - Tp) := (add_tsub_cancel_of_le hTp).symm
  have hc : card Tn = card (Mp - Tp) + 1 := by
    have h₁ := congrArg card hT'
    have h₂ := congrArg card hMp
    rw [card_add] at h₁ h₂
    omega
  have hn : Tn.sum ≤ card Tn • γ :=
    sum_le_card_nsmul _ _ fun a ha ↦ not_lt.mp (of_mem_filter (p := fun a ↦ ¬γ < a) ha)
  have hp : card (Mp - Tp) • γ ≤ (Mp - Tp).sum :=
    card_nsmul_le_sum fun a ha ↦
      (of_mem_filter (p := (γ < ·)) (mem_of_le (Multiset.sub_le_self _ _) ha)).le
  calc T.sum = Tp.sum + Tn.sum := by rw [hT']; simp
    _ ≤ Tp.sum + (card (Mp - Tp) • γ + γ) := by
      gcongr
      rwa [hc, succ_nsmul] at hn
    _ ≤ Tp.sum + ((Mp - Tp).sum + γ) := by gcongr
    _ = Mp.sum + γ := by
      conv_rhs => rw [hMp]
      simp [add_assoc]

/-- If all elements of `s` are at most `γ` and the sum of `s` is `card s • γ`, then all elements
of `s` are equal to `γ`. -/
theorem eq_of_le_of_sum_eq {s : Multiset α} {γ : α} (hle : ∀ a ∈ s, a ≤ γ)
    (hsum : s.sum = card s • γ) : ∀ a ∈ s, a = γ := by
  intro a ha
  by_contra hne
  have hlt : a < γ := lt_of_le_of_ne (hle a ha) hne
  have hs := cons_erase ha
  have hle' : (s.erase a).sum ≤ card (s.erase a) • γ :=
    sum_le_card_nsmul _ _ fun b hb ↦ hle b (mem_of_mem_erase hb)
  have : s.sum < card s • γ := by
    rw [← hs, sum_cons, card_cons, succ_nsmul, add_comm (card (s.erase a) • γ)]
    exact add_lt_add_of_lt_of_le hlt hle'
  exact this.ne hsum

end Multiset
