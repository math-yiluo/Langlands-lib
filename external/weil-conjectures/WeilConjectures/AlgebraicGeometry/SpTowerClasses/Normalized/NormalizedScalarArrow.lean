/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Shift.Adjunction
/-! # Transposition of a scalar arrow with normalized endpoints -/
@[expose] public section
set_option autoImplicit false
open CategoryTheory
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- Naturality of a shift-compatible adjunction gives the normalized transpose.
Source: adjunction unit naturality and its commutation with shifts.
(blueprint: lem-sfb-normalized-scalar-arrow). -/
theorem normalizedScalarArrow_transpose
    {A B : Type*} [Category A] [Category B] [HasShift A ℤ] [HasShift B ℤ]
    (L : A ⥤ B) (R : B ⥤ A) [L.CommShift ℤ] [R.CommShift ℤ]
    (ad : L ⊣ R) [ad.CommShift ℤ]
    {X Y XR YR : A} {X' Y' : B}
    (e : L.obj X ≅ X') (a : L.obj Y ⟶ Y')
    (ux : R.obj X' ≅ XR) (uy : R.obj Y' ≅ YR)
    (q : X ⟶ XR) (r : Y ⟶ YR)
    (hx : ad.unit.app X ≫ R.map e.hom ≫ ux.hom = q)
    (hy : ad.unit.app Y ≫ R.map a ≫ uy.hom = r)
    (n : ℤ) (f : X ⟶ Y⟦n⟧) :
    q ≫ ux.inv ≫ R.map (e.inv ≫ L.map f ≫
        (L.commShiftIso n).hom.app Y ≫ a⟦n⟧') ≫
        (R.commShiftIso n).hom.app Y' ≫ uy.hom⟦n⟧' = f ≫ r⟦n⟧' := by
  rw [← hx]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]
  rw [← R.map_comp_assoc, Iso.hom_inv_id, R.map_id, Category.id_comp]
  have hn := ad.unit.naturality f
  simp only [Functor.id_map, Functor.comp_map] at hn
  rw [← reassoc_of% hn]
  rw [R.commShiftIso_hom_naturality_assoc]
  have hu := ad.unit_app_commShiftIso_hom_app ℤ n Y
  simp only [Functor.commShiftIso_comp_hom_app] at hu
  rw [reassoc_of% hu]
  simp only [← (shiftFunctor A n).map_comp, hy]
end AlgebraicGeometry.ProEtale.SpTowerClasses
