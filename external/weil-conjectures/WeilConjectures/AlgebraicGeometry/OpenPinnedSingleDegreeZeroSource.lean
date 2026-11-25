/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.PinnedSingleBaseChangeShift
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenBaseChangeComparisons

/-! # Constructed source comparison for the degree-zero open square
Source: Stacks Project, Tags 08FE, 08HY and 08DW.
(blueprint: def-pc-open-pinned-single-degree-zero-source). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry

/-- The source comparison, constructed from the pinned pullback composition,
exact open pullback, the sectionwise derived direct-image comparison, and exact
restriction of the single complex. No resolution or isomorphism is selected from
an arbitrary existence statement.
Source: Stacks Project, Tags 08FE, 08HY and 08DW.
(blueprint: def-pc-open-pinned-single-degree-zero-source). -/
def openPinnedSingleDegreeZeroSourceIso
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (V : S.Opens) (W : S'.Opens) (hWV : W ≤ g ⁻¹ᵁ V) :
    singleDegreeBaseChangeSource.{u, w} f g 0 ⋙
        (schemeOpenRestriction S' W).mapDerivedCategory ≅
      schemeOpenRestriction X (f ⁻¹ᵁ V) ⋙
        singleDegreeBaseChangeSource.{u, w} (f ∣_ V) (g.resLE V W hWV) 0 := by
  classical
  let c := @Classical.choose _ _ (Classical.choose_spec (Classical.choose_spec
    (Classical.choose_spec exists_derivedPullbackComposition.{u, w})))
  let gA := g.resLE V W hWV
  let sX := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0
  let RX := schemeOpenRestriction X (f ⁻¹ᵁ V)
  let e : derivedPullback g ⋙ (schemeOpenRestriction S' W).mapDerivedCategory ≅
      (schemeOpenRestriction S V).mapDerivedCategory ⋙ derivedPullback gA :=
    Functor.isoWhiskerLeft _ (singleComplexOpenPullbackIso S' W).symm ≪≫
      c W.ι g ≪≫
      eqToIso (congrArg (fun k ↦ derivedPullback k)
        (Scheme.Hom.resLE_comp_ι g hWV).symm) ≪≫
      (c gA V.ι).symm ≪≫
      Functor.isoWhiskerRight (singleComplexOpenPullbackIso S V) _
  change (sX ⋙ schemeDerivedDirectImage f) ⋙ derivedPullback g ⋙
      (schemeOpenRestriction S' W).mapDerivedCategory ≅
    RX ⋙ (DerivedCategory.singleFunctor _ 0 ⋙ schemeDerivedDirectImage (f ∣_ V)) ⋙
      derivedPullback gA
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft sX
      (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ e ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (singleComplexOpenDirectImageIso f V)
          (derivedPullback gA)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (RX.mapDerivedCategorySingleFunctor 0)
      (schemeDerivedDirectImage (f ∣_ V) ⋙ derivedPullback gA) ≪≫
    Functor.associator _ _ _

-- Identifying the reassociated functor categories needs additional elaboration heartbeats.
set_option backward.isDefEq.respectTransparency.types false in
/-- Component formula for the constructed source isomorphism.
Source: Stacks Project, Tags 08FE and 08HY.
(blueprint: def-pc-open-pinned-single-degree-zero-source). -/
theorem openPinnedSingleDegreeZeroSourceIso_app
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (V : S.Opens) (W : S'.Opens) (hWV : W ≤ g ⁻¹ᵁ V) (G : X.Modules) :
    (openPinnedSingleDegreeZeroSourceIso f g V W hWV).hom.app G =
      (singleComplexOpenBaseChangeSourceIso f g
        ((DerivedCategory.singleFunctor _ 0).obj G) V W hWV).hom ≫
      (derivedPullback (g.resLE V W hWV)).map
        ((schemeDerivedDirectImage (f ∣_ V)).map
          (((schemeOpenRestriction X (f ⁻¹ᵁ V)).mapDerivedCategorySingleFunctor 0).hom.app G))
      := by
  simp only [openPinnedSingleDegreeZeroSourceIso, singleComplexOpenBaseChangeSourceIso,
    id_eq, Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.comp_map, Iso.symm_hom, Iso.app_hom, Functor.mapIso_hom,
    eqToIso.hom, eqToHom_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.assoc, Category.id_comp, Category.comp_id]
  change (𝟙 _ ≫ _) = _
  exact Category.id_comp _

end AlgebraicGeometry
