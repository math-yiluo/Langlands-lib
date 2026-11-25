/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Multiset.MapFold

/-!
# Sub-multisets of an image

A sub-multiset of the image `s.map f` of a multiset is itself the image of a sub-multiset of `s`.
-/

@[expose] public section

namespace Multiset

variable {α β : Type*}

/-- A sub-multiset of `s.map f` is the image of a sub-multiset of `s`. -/
theorem exists_le_map_eq_of_le_map {f : α → β} {s : Multiset α} {t : Multiset β}
    (h : t ≤ s.map f) : ∃ u ≤ s, u.map f = t := by
  classical
  induction s using Multiset.induction_on generalizing t with
  | empty =>
    rw [map_zero, le_zero] at h
    exact ⟨0, zero_le _, by rw [h, map_zero]⟩
  | cons a s ih =>
    rw [map_cons] at h
    by_cases ha : f a ∈ t
    · obtain ⟨t', rfl⟩ := exists_cons_of_mem ha
      obtain ⟨u, hu, rfl⟩ := ih ((cons_le_cons_iff _).1 h)
      exact ⟨a ::ₘ u, (cons_le_cons_iff _).2 hu, by rw [map_cons]⟩
    · obtain ⟨u, hu, rfl⟩ := ih ((le_cons_of_notMem ha).1 h)
      exact ⟨u, hu.trans (le_cons_self _ _), rfl⟩

end Multiset
