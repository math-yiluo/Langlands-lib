/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.Basic
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Detecting isomorphisms on shifted test objects

In a category with a shift by `ℤ`, every object is isomorphic to a shift `N⟦n⟧` (namely of
`N = X⟦-n⟧`). Hence a morphism `u` is an isomorphism as soon as composition with `u` is bijective
on morphisms out of all objects of the form `N⟦n⟧`
(`CategoryTheory.isIso_of_bijective_comp_shift`).
-/

@[expose] public section

namespace CategoryTheory

variable {C : Type*} [Category C] [HasShift C ℤ]

/-- A morphism `u : X ⟶ Y` is an isomorphism as soon as composition with `u` is bijective on
morphisms out of every shifted object `N⟦n⟧`, for a fixed `n : ℤ`. -/
theorem isIso_of_bijective_comp_shift (n : ℤ) {X Y : C} (u : X ⟶ Y)
    (h : ∀ N : C, Function.Bijective (fun g : N⟦n⟧ ⟶ X ↦ g ≫ u)) : IsIso u := by
  refine isIso_of_yoneda_map_bijective u (fun Z ↦ ?_)
  let e : (Z⟦-n⟧)⟦n⟧ ≅ Z := (shiftFunctorCompIsoId C (-n) n (by omega)).app Z
  have hc : (fun x : Z ⟶ X ↦ x ≫ u) =
      (fun g : (Z⟦-n⟧)⟦n⟧ ⟶ Y ↦ e.inv ≫ g) ∘ (fun g ↦ g ≫ u) ∘ (fun x ↦ e.hom ≫ x) := by
    funext x
    simp
  rw [hc]
  exact ((isIso_iff_coyoneda_map_bijective e.inv).1 inferInstance _).comp
    ((h _).comp ((isIso_iff_coyoneda_map_bijective e.hom).1 inferInstance _))

omit [HasShift C ℤ] in
/-- Changing the sum in `shiftFunctorAdd'` amounts to composing with an `eqToHom`. -/
@[reassoc]
lemma shiftFunctorAdd'_inv_app_comp_eqToHom {A : Type*} [AddMonoid A] [HasShift C A]
    (a b c c' : A) (h : a + b = c) (h' : a + b = c') (X : C) :
    (shiftFunctorAdd' C a b c h).inv.app X ≫ eqToHom (by rw [← h, ← h']) =
      (shiftFunctorAdd' C a b c' h').inv.app X := by
  subst h h'
  simp

end CategoryTheory
