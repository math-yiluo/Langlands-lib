/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts

/-!
# Biproducts with all but one summand zero

A biproduct whose summands are all zero is zero, and a morphism into a biproduct all of whose
summands but one are zero is an isomorphism as soon as its component in the remaining summand
is one.
-/

@[expose] public section

namespace CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C] {J : Type w} {f : J → C}
  [HasBiproduct f]

/-- A biproduct of zero objects is zero. -/
lemma biproduct.isZero_of_forall_isZero (h : ∀ j, IsZero (f j)) : IsZero (⨁ f) :=
  (IsZero.iff_id_eq_zero _).2 (biproduct.hom_ext _ _ fun j ↦ (h j).eq_of_tgt _ _)

/-- A morphism `biproduct.lift g : W ⟶ ⨁ f` into a biproduct all of whose summands but `f k`
are zero is an isomorphism if its component `g k` is one: its inverse is `π_k ≫ (g k)⁻¹`. -/
lemma biproduct.isIso_lift_of_isZero {W : C} (g : ∀ j, W ⟶ f j) (k : J) [IsIso (g k)]
    (h : ∀ j, j ≠ k → IsZero (f j)) : IsIso (biproduct.lift g) := by
  classical
  refine ⟨biproduct.π f k ≫ inv (g k), by simp, biproduct.hom_ext _ _ fun j ↦ ?_⟩
  by_cases hj : j = k
  · subst hj
    simp
  · exact (h j hj).eq_of_tgt _ _

end CategoryTheory.Limits
