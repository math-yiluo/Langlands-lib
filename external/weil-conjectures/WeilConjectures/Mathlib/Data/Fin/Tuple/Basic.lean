/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Data.Fin.Tuple.Basic

/-!
# The range of a concatenated tuple

The range of `Fin.append a b` is the union of the ranges of `a` and `b`.
-/

@[expose] public section

/-- The range of `Fin.append a b` is the union of the ranges. -/
lemma Fin.range_append {α : Type*} {m n : ℕ} (a : Fin m → α) (b : Fin n → α) :
    Set.range (Fin.append a b) = Set.range a ∪ Set.range b := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    induction k using Fin.addCases with
    | left k => exact Or.inl ⟨k, (Fin.append_left a b k).symm⟩
    | right k => exact Or.inr ⟨k, (Fin.append_right a b k).symm⟩
  · rintro (⟨k, rfl⟩ | ⟨k, rfl⟩)
    · exact ⟨Fin.castAdd n k, by simp⟩
    · exact ⟨Fin.natAdd m k, by simp⟩
