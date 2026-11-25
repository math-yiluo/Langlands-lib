/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.GroupTheory.Exponent

/-!
# Homomorphisms with finite image have finite order

A homomorphism into a commutative group whose image is finite is an element of finite order of
the group of homomorphisms.
-/

@[expose] public section

namespace MonoidHom

/-- A homomorphism into a commutative group with finite image has finite order. -/
theorem isOfFinOrder_of_finite_range {W A : Type*} [Group W] [CommGroup A] {χ : W →* A}
    (hχ : (Set.range χ).Finite) : IsOfFinOrder χ := by
  have : Finite χ.range := by
    rw [← MonoidHom.coe_range] at hχ
    exact hχ.to_subtype
  refine isOfFinOrder_iff_pow_eq_one.2
    ⟨Monoid.exponent χ.range, Nat.pos_of_ne_zero Monoid.exponent_ne_zero_of_finite, ?_⟩
  ext w
  simpa using congr_arg Subtype.val (Monoid.pow_exponent_eq_one (⟨χ w, w, rfl⟩ : χ.range))

end MonoidHom
