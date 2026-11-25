/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Functor
public import Mathlib.CategoryTheory.Triangulated.TriangleShift

/-!
# The shift functors of a pretriangulated category are triangulated

Let `C` be a preadditive category with a shift by `ℤ`. For `n : ℤ`, the shift functor
`X ↦ X⟦n⟧` commutes with the shifts: its commutation isomorphism with the shift by `a` is
`(-1)^{an}` times the canonical isomorphism `X⟦a⟧⟦n⟧ ≅ X⟦n⟧⟦a⟧`
(`CategoryTheory.Pretriangulated.commShiftShiftFunctor`). The sign is forced: with it the image
of a triangle under `X ↦ X⟦n⟧` is isomorphic to the triangle `Triangle.shiftFunctor C n`, whose
three morphisms are multiplied by `(-1)^n`, so that when `C` is pretriangulated the shift
functors are triangulated (`CategoryTheory.Pretriangulated.isTriangulated_shiftFunctor`).
Without the sign the image of a distinguished triangle would have all three morphisms of the
wrong sign for odd `n`, and need not be distinguished.
-/

@[expose] public section

namespace CategoryTheory.Pretriangulated

open Category Limits

variable (C : Type*) [Category* C] [Preadditive C] [HasShift C ℤ]
  [∀ (n : ℤ), (shiftFunctor C n).Additive]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The shift functor `X ↦ X⟦n⟧` commutes with the shift by `a` through `(-1)^{an}` times the
canonical isomorphism `X⟦a⟧⟦n⟧ ≅ X⟦n⟧⟦a⟧`. -/
noncomputable instance commShiftShiftFunctor (n : ℤ) : (shiftFunctor C n).CommShift ℤ where
  commShiftIso a := (a * n).negOnePow • shiftFunctorComm C a n
  commShiftIso_zero := by
    refine Iso.ext (NatTrans.ext (funext fun X ↦ ?_))
    rw [Functor.CommShift.isoZero_hom_app, Preadditive.smul_iso_hom, NatTrans.app_units_zsmul,
      zero_mul, Int.negOnePow_zero, one_smul, ← shiftFunctorComm_symm C n 0, Iso.symm_hom,
      ← cancel_epi ((shiftFunctorComm C n 0).hom.app X), Iso.hom_inv_id_app,
      shiftFunctorComm_zero_hom_app, assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    simp
  commShiftIso_add a b := by
    refine Iso.ext (NatTrans.ext (funext fun X ↦ ?_))
    simp only [Functor.CommShift.isoAdd_hom_app, Preadditive.smul_iso_hom,
      NatTrans.app_units_zsmul, Functor.map_units_smul, Linear.units_smul_comp,
      Linear.comp_units_smul, smul_smul, ← Int.negOnePow_add, add_mul]
    congr 1
    rw [← shiftFunctorComm_symm C n, ← shiftFunctorComm_symm C n,
      ← shiftFunctorComm_symm C n]
    dsimp only [Iso.symm_hom]
    rw [← cancel_epi ((shiftFunctorComm C n (a + b)).hom.app X), Iso.hom_inv_id_app,
      ← cancel_mono ((shiftFunctorAdd C a b).hom.app ((shiftFunctor C n).obj X))]
    simp only [assoc, Iso.inv_hom_id_app, comp_id, Functor.comp_obj]
    rw [shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app_assoc]
    simp [← Functor.map_comp]

lemma shiftFunctor_commShiftIso_hom_app (n a : ℤ) (X : C) :
    ((shiftFunctor C n).commShiftIso a).hom.app X =
      (a * n).negOnePow • (shiftFunctorComm C a n).hom.app X :=
  rfl

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- In a pretriangulated category the shift functors are triangulated: the image of a
distinguished triangle `T` under `X ↦ X⟦n⟧` is isomorphic to the distinguished triangle
`Triangle.shiftFunctor C n T`, through `(-1)^n` on the second object. -/
instance isTriangulated_shiftFunctor [HasZeroObject C] [Pretriangulated C] (n : ℤ) :
    (shiftFunctor C n).IsTriangulated where
  map_distinguished T hT := isomorphic_distinguished _ (Triangle.shift_distinguished T hT n) _
    (Triangle.isoMk _ _ (Iso.refl _) (n.negOnePow • Iso.refl _) (Iso.refl _)
      (by simp) (by simp [smul_smul]) (by simp [shiftFunctor_commShiftIso_hom_app]))

end CategoryTheory.Pretriangulated
