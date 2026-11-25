/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Field.IsField

/-!
# Fields as commutative rings with inverses

A commutative ring is a field (`IsField`) if and only if `0 ≠ 1` and every nonzero element has a
multiplicative inverse.
-/

@[expose] public section

/-- **Fields.** A commutative ring `R` is a field if and only if `0 ≠ 1` in `R` and every nonzero
element of `R` has a multiplicative inverse.

(blueprint: `def-weil-field`) -/
theorem isField_iff_exists_mul_eq_one {R : Type*} [CommRing R] :
    IsField R ↔ (0 : R) ≠ 1 ∧ ∀ x : R, x ≠ 0 → ∃ y, x * y = 1 := by
  refine ⟨fun h ↦ ⟨fun e ↦ ?_, fun x hx ↦ h.mul_inv_cancel hx⟩,
    fun ⟨h0, h⟩ ↦ ⟨⟨0, 1, h0⟩, mul_comm, fun hx ↦ h _ hx⟩⟩
  obtain ⟨a, b, hab⟩ := h.exists_pair_ne
  exact hab (by rw [← mul_one a, ← mul_one b, ← e, mul_zero, mul_zero])
