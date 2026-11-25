/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Roots of a product of factors `1 - a * X`

The roots of `∏ (1 - aᵢ * X)` over a field are the inverses of the `aᵢ`, provided no `aᵢ`
vanishes, and mapping such a product along a ring homomorphism maps its factors.
-/

@[expose] public section

namespace Polynomial

variable {K : Type*} [Field K]

theorem roots_one_sub_C_mul_X {a : K} (ha : a ≠ 0) : (1 - C a * X : K[X]).roots = {a⁻¹} := by
  have h : (1 - C a * X : K[X]) = C (-a) * X + C 1 := by rw [C_neg, C_1, neg_mul]; ring
  rw [h, roots_C_mul_X_add_C _ (neg_ne_zero.mpr ha)]
  simp

/-- The roots of `∏ (1 - a * X)` are the inverses of the `a`. -/
theorem roots_multiset_prod_one_sub_C_mul_X {s : Multiset K} (hs : (0 : K) ∉ s) :
    ((s.map fun a ↦ 1 - C a * X).prod).roots = s.map (·⁻¹) := by
  have hne : ∀ a : K, (1 - C a * X : K[X]) ≠ 0 := by
    intro a h
    simpa using congrArg (coeff · 0) h
  rw [roots_multiset_prod, Multiset.bind_map]
  · rw [Multiset.bind_congr (g := fun a ↦ ({a⁻¹} : Multiset K))
      (fun a ha ↦ roots_one_sub_C_mul_X (fun h ↦ hs (h ▸ ha))), Multiset.bind_singleton]
  · simp only [Multiset.mem_map]
    rintro ⟨a, -, h⟩
    exact hne a h

/-- Mapping `∏ (1 - a * X)` along a ring homomorphism `f` gives `∏ (1 - f a * X)`. -/
theorem map_multiset_prod_one_sub_C_mul_X {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
    (s : Multiset R) :
    ((s.map fun a ↦ 1 - C a * X).prod).map f = ((s.map f).map fun a ↦ 1 - C a * X).prod := by
  rw [Polynomial.map_multiset_prod, Multiset.map_map, Multiset.map_map]
  exact congrArg _ (Multiset.map_congr rfl fun a _ ↦ by simp)

end Polynomial
