/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Tactic.Ring

/-!
# An alternating telescoping sum

`∑_{q = 0}^{n} (-1)^q (a_q + a_{q-1}) = (-1)^n a_n + a_{-1}`: this is the computation showing that
the Euler characteristic of a bounded complex of finite dimensional vector spaces is that of its
cohomology.
-/

@[expose] public section

namespace Finset

/-- The alternating telescoping sum `∑_{q = 0}^{n} (-1)^q (a_q + a_{q-1}) = (-1)^n a_n + a_{-1}`. -/
theorem sum_range_neg_one_pow_mul_add_sub_one {R : Type*} [CommRing R] (a : ℤ → R) (n : ℕ) :
    ∑ q ∈ range (n + 1), (-1) ^ q * (a q + a (q - 1)) = (-1) ^ n * a n + a (-1) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih, pow_succ]
    push_cast
    ring_nf

end Finset
