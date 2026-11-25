/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.GroupWithZero.Basic
public import Mathlib.Data.Nat.Cast.Basic

/-!
# Powers of natural numbers which are nonzero in a semiring without zero divisors

## Main statements

- `NeZero.natCast_pow`: if the image of `ℓ` in a semiring without zero divisors is nonzero, so
  is the image of `ℓ ^ n`.
-/

@[expose] public section

/-- If the image of a natural number `ℓ` in a semiring without zero divisors is nonzero, then so
is the image of `ℓ ^ n`. -/
lemma NeZero.natCast_pow {R : Type*} [Semiring R] [NoZeroDivisors R] (ℓ n : ℕ)
    [NeZero (ℓ : R)] : NeZero ((ℓ ^ n : ℕ) : R) :=
  Nat.cast_pow (α := R) ℓ n ▸ NeZero.pow
