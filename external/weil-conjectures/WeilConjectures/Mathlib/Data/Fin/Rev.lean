/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Data.Fin.Rev

/-!
# The sign `(-1) ^ i` under `Fin.rev`

## Main statements

- `Fin.neg_one_pow_rev`: `(-1) ^ i` is invariant under `i ↦ 2 d - i` on `Fin (2 * d + 1)`.
-/

@[expose] public section

namespace Fin

/-- The sign `(-1)ⁱ` is invariant under `i ↦ 2 d - i`. -/
theorem neg_one_pow_rev {R : Type*} [Monoid R] [HasDistribNeg R] {d : ℕ}
    (i : Fin (2 * d + 1)) : (-1 : R) ^ (i.rev : ℕ) = (-1) ^ (i : ℕ) := by
  have h : (i.rev : ℕ) + 2 * i = 2 * d + i := by simp only [Fin.val_rev]; omega
  have := congrArg (fun n : ℕ ↦ (-1 : R) ^ n) h
  simpa [pow_add, pow_mul] using this

end Fin
