/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Ring.NegOnePow

/-!
# The sign of a natural number

The sign `(-1) ^ i` of an integer which is a natural number `i` is the power `(-1) ^ i` in `ℤˣ`.
-/

@[expose] public section

/-- The sign `(-1) ^ i` of a natural number `i`, seen as an integer. -/
lemma Int.negOnePow_natCast_eq_pow (i : ℕ) : (i : ℤ).negOnePow = (-1 : ℤˣ) ^ i := by
  rw [Int.negOnePow_def, zpow_natCast]
