/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Ring.Idempotent
public import Mathlib.Tactic.NoncommRing

/-!
# Lifting idempotents modulo a square-zero element

If `x² - x` has square zero in a ring, then `3x² - 2x³` is idempotent.
-/

@[expose] public section

/-- If `(x² - x)² = 0` in a ring, then `3x² - 2x³` is idempotent (written without numerals). -/
lemma idem_of_sub_mul_sub_eq_zero {R : Type*} [Ring R] (x : R)
    (h : (x * x - x) * (x * x - x) = 0) :
    (x * x + x * x + x * x - x * x * x - x * x * x) *
      (x * x + x * x + x * x - x * x * x - x * x * x) =
      x * x + x * x + x * x - x * x * x - x * x * x := by
  have key : (x * x + x * x + x * x - x * x * x - x * x * x) *
      (x * x + x * x + x * x - x * x * x - x * x * x) -
      (x * x + x * x + x * x - x * x * x - x * x * x) =
      (x * x - x) * (x * x - x) * (x * x + x * x + x * x + x * x - x - x - x - x - 1 - 1 - 1) := by
    noncomm_ring
  rw [h, zero_mul, sub_eq_zero] at key
  exact key
