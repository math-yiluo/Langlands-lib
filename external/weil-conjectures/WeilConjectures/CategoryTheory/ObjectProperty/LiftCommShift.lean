/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
# The commutation of a lift to a full subcategory with the shifts

For a property `P` of objects of `C` stable under the shifts and a functor `F : E ⥤ C` commuting
with the shifts whose values satisfy `P`, the lift `P.lift F hF : E ⥤ P.FullSubcategory`
commutes with the shifts (`Functor.CommShift.ofComp`). This file computes its commutation
isomorphism on the underlying objects: it is the commutation isomorphism of `F`, followed by
the inverse of that of the inclusion `P.ι`
(`CategoryTheory.ObjectProperty.ι_map_lift_commShiftIso_hom_app`).
-/

@[expose] public section

namespace CategoryTheory.ObjectProperty

variable {C E A : Type*} [Category* C] [Category* E] [AddMonoid A] [HasShift C A] [HasShift E A]
  (P : ObjectProperty C) [P.IsStableUnderShift A] (F : E ⥤ C) (hF : ∀ X, P (F.obj X))
  [F.CommShift A]

/-- The commutation of the lift `P.lift F hF` with the shifts is, on the underlying objects, the
commutation of `F` with the shifts followed by the inverse of that of the inclusion. -/
lemma ι_map_lift_commShiftIso_hom_app (a : A) (X : E) :
    P.ι.map (((P.lift F hF).commShiftIso a).hom.app X) =
      (F.commShiftIso a).hom.app X ≫ (P.ι.commShiftIso a).inv.app ((P.lift F hF).obj X) := by
  have h := NatTrans.shift_app_comm (P.liftCompιIso F hF).hom a X
  simp only [Functor.commShiftIso_comp_hom_app] at h
  rw [← cancel_mono ((P.ι.commShiftIso a).hom.app ((P.lift F hF).obj X)), Category.assoc,
    Iso.inv_hom_id_app]
  simpa [liftCompιIso] using h.trans (Category.comp_id _).symm

end CategoryTheory.ObjectProperty
