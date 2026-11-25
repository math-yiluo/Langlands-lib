/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.FieldTheory.Separable

@[expose] public section
universe u
set_option autoImplicit false

/-- The minimal polynomial of a separable element gives a nonzero separable
polynomial whose coefficients are evaluated through any specified field map.
The proof is the standard minimal-polynomial argument. -/
theorem exists_separable_polynomial_of_isSeparable
    {K L : Type u} [Field K] [Field L] [Algebra K L]
    (f : K →+* L) (hf : algebraMap K L = f) (y : L)
    (hy : IsSeparable K y) :
    ∃ p : Polynomial K, p ≠ 0 ∧ p.Separable ∧ p.eval₂ f y = 0 := by
  refine ⟨minpoly K y, minpoly.ne_zero hy.isIntegral, hy, ?_⟩
  rw [← hf]
  exact minpoly.aeval K y
