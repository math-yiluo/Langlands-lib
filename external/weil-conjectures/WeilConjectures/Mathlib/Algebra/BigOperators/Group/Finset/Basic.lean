/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Transporting an identity between sums

An identity `∑ _a, g = ∑ a, y a` between a sum of a constant family and a sum transports along
equalities `f = g` and `y a = z a` (`Finset.sum_const_eq_sum_of_eq`).
-/

@[expose] public section

/-- Transport of an identity `∑ _a, g = ∑ a, y a` along equalities `f = g` and `y a = z a`.

The additive structure is an implicit argument rather than an instance argument, so that it is
determined by unification with the goal: this avoids comparing different (but definitionally
equal) instances in the kernel. -/
lemma Finset.sum_const_eq_sum_of_eq {β : Type*} {_ : AddCommMonoid β} {κ : Type*}
    {_ : Fintype κ} {f g : β} (y z : κ → β) (hf : f = g) (hg : ∑ _a : κ, g = ∑ a, y a)
    (hy : ∀ a, y a = z a) : ∑ _a : κ, f = ∑ a, z a := by
  rw [hf, hg]
  exact Finset.sum_congr rfl fun a _ ↦ hy a
