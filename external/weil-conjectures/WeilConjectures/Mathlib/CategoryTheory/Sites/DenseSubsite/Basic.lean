/-
Copyright (c) 2026 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.Basic

/-!
# Basic

Ported from the `proetale` package (`Proetale.Mathlib.CategoryTheory.Sites.DenseSubsite.Basic`).
-/

@[expose] public section

namespace CategoryTheory

namespace Functor

variable {C D : Type*} [Category* C] [Category* D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  (G : C ⥤ D) (A : Type*) [Category* A]

lemma IsCoverDense.restrictHomEquivHom_symm_apply [G.IsCoverDense K]
    [G.IsLocallyFull K] {F : Dᵒᵖ ⥤ A} {F' : Sheaf K A}
    (f : F ⟶ F'.obj) :
    restrictHomEquivHom (G := G).symm f = G.op.whiskerLeft f :=
  rfl

namespace IsDenseSubsite

variable [IsDenseSubsite J K G]
  [(G.sheafPushforwardContinuous A J K).IsEquivalence]
  [HasWeakSheafify J A]

@[reassoc (attr := simp)]
lemma toSheafify_sheafifyOfIsEquivalenceCompIso_inv_app_hom (F : Dᵒᵖ ⥤ A) :
    dsimp% toSheafify J (G.op ⋙ F) ≫
      ((sheafifyOfIsEquivalenceCompIso J K G A).inv.app F).hom =
      G.op.whiskerLeft ((sheafifyAdjunctionOfIsEquivalence _ _ _ _).unit.app _) := by
  have := isLocallyFull J K G
  have := isCoverDense J K G
  simp only [sheafifyOfIsEquivalenceCompIso, isoWhiskerLeft_trans, isoWhiskerLeft_twice,
    Iso.trans_assoc, Iso.trans_inv, isoWhiskerLeft_inv, Category.assoc, Iso.symm_inv,
    NatTrans.comp_app, whiskerLeft_app,
    rightUnitor_inv_app, associator_inv_app, associator_hom_app, Category.comp_id, Category.id_comp,
    sheafifyAdjunctionOfIsEquivalence, sheafifyHomEquivOfIsEquivalence,
    ObjectProperty.ι_obj,
    Adjunction.mkOfHomEquiv_unit_app, Equiv.trans_apply]
  rw [← IsCoverDense.restrictHomEquivHom_symm_apply]
  erw [Equiv.symm_apply_apply]
  erw [CategoryTheory.Adjunction.homEquiv_id]
  rw [toSheafify]
  simp only [sheafificationAdjunction_unit_app, ObjectProperty.FullSubcategory.comp_hom,
    ObjectProperty.FullSubcategory.id_hom, Equivalence.toAdjunction_unit, Equivalence.symm_unit]
  erw [Category.id_comp, Category.comp_id]
  rfl

variable [HasWeakSheafify K A]

@[reassoc (attr := simp)]
lemma toSheafify_sheafEquivSheafificationCompatibility_hom_app_hom (F : Dᵒᵖ ⥤ A) :
    toSheafify _ _ ≫ ((sheafEquivSheafificationCompatibility J K G A).hom.app F).hom =
      Functor.whiskerLeft G.op (toSheafify _ _) := by
  simp only [sheafEquivSheafificationCompatibility, sheafPushforwardContinuous, Iso.trans_hom,
    Iso.symm_hom, isoWhiskerRight_hom, NatTrans.comp_app, whiskerRight_app,
    ObjectProperty.lift_map, comp_map, ObjectProperty.ι_obj, ObjectProperty.ι_map,
    whiskeringLeft_obj_map, ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom]
  erw [toSheafify_sheafifyOfIsEquivalenceCompIso_inv_app_hom_assoc]
  rw [← whiskerLeft_comp]
  erw [Adjunction.unit_leftAdjointUniq_hom_app (sheafifyAdjunctionOfIsEquivalence J K G A)
    (sheafificationAdjunction K A) F]

/-- If the restriction `G.op ⋙ P` of a presheaf `P` to a dense subsite is already a sheaf, then
sheafification does not change the sections of `P` over the objects of the subsite. -/
lemma isIso_whiskerLeft_toSheafify (P : Dᵒᵖ ⥤ A) (hP : Presheaf.IsSheaf J (G.op ⋙ P)) :
    IsIso (G.op.whiskerLeft (toSheafify K P)) := by
  rw [← toSheafify_sheafEquivSheafificationCompatibility_hom_app_hom J K G A P]
  have : IsIso (toSheafify J (G.op ⋙ P)) := isIso_toSheafify J hP
  have : IsIso ((sheafEquivSheafificationCompatibility J K G A).hom.app P).hom :=
    (sheafToPresheaf J A).map_isIso ((sheafEquivSheafificationCompatibility J K G A).hom.app P)
  exact IsIso.comp_isIso (f := toSheafify J (G.op ⋙ P))

end Functor.IsDenseSubsite

end CategoryTheory
