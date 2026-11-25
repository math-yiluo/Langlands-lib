/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar

/-! # Identity direct-image comparison across the bounded-below inclusion -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

private theorem inverse_identity_conjugate
    {C : Type*} [Category C] {L R : C ⥤ C} (a : L ⊣ R) (e : L ≅ 𝟭 C) (K : C) :
    ((conjugateIsoEquiv a Adjunction.id e.symm).inv.app K) =
      a.unit.app K ≫ R.map (e.hom.app K) := by
  simp [conjugateIsoEquiv_apply_inv, conjugateEquiv, mateEquiv, Adjunction.id]

private theorem plus_identity_unit
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    let e := Functor.mapDerivedCategoryPlusNatIso
      (upperStarId (ModuleCat.{u + 1} Λ) X) ≪≫ Functor.mapDerivedCategoryPlusIdIso _
    let d := Functor.rightDerivedFunctorPlusNatIso
      (lowerStarId (ModuleCat.{u + 1} Λ) X) ≪≫ Functor.rightDerivedFunctorPlusIdIso _
    (derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (𝟙 X)).unit.app K ≫
      (lowerStar (ModuleCat.{u + 1} Λ) (𝟙 X)).rightDerivedFunctorPlus.map (e.hom.app K) =
        d.inv.app K := by
  let C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)
  let R := lowerStar (ModuleCat.{u + 1} Λ) (𝟙 X)
  let a := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)
  let e := upperStarId (ModuleCat.{u + 1} Λ) X
  let d := lowerStarId (ModuleCat.{u + 1} Λ) X
  have h (M : C) : a.unit.app M ≫ R.map (e.hom.app M) = d.inv.app M := by
    have hc := unit_conjugateEquiv Adjunction.id a e.hom M
    have hd := congrArg (fun z ↦ z.hom.app M)
      (conjugateIsoEquiv_upperStarId (ModuleCat.{u + 1} Λ) X)
    simp only [conjugateIsoEquiv_apply_hom, Iso.symm_hom] at hd
    change ((conjugateEquiv Adjunction.id a) e.hom).app M = d.inv.app M at hd
    simp only [Adjunction.id_unit, NatTrans.id_app, Category.id_comp, Functor.id_obj] at hc
    exact hc.symm.trans hd
  have hu := a.derivedPlus_unit_comp_app Adjunction.id e d.symm h K
  have hv := congrArg (fun z ↦ z ≫ R.rightDerivedFunctorPlus.map
    ((Functor.mapDerivedCategoryPlusIdIso C).hom.app K)) hu
  rw [Adjunction.derivedPlus_id_unit] at hv
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Iso.symm_hom, Category.assoc] at hv
  have hn := (Functor.rightDerivedFunctorPlusNatTrans d.inv).naturality
    ((Functor.mapDerivedCategoryPlusIdIso C).hom.app K)
  have hi := (Functor.rightDerivedFunctorPlusIdIso C).inv.naturality
    ((Functor.mapDerivedCategoryPlusIdIso C).hom.app K)
  dsimp only [Functor.id_map, Functor.comp_map] at hn hi
  rw [← hn, ← reassoc_of% hi, Iso.inv_hom_id_app_assoc] at hv
  simpa only [derivedUpperStarLowerStarAdjunctionPlus,
    Adjunction.derivedAdjunctionPlus_eq_derivedPlus, Iso.trans_hom, Iso.trans_inv,
    NatTrans.comp_app, Functor.map_comp, Functor.rightDerivedFunctorPlusNatIso,
    Iso.symm_hom, a, R, e, d, C, Functor.id_obj, Category.assoc] using hv

/-- The canonical identity direct-image normalization agrees across D+ inclusion.
Source: Step 3 of lem-pur-refinement-mate-plus-compatibility; Stacks Tags 015F
and 0B65 (blueprint: lem-pur-identity-push-plus-inclusion).

Proof: conjugate the inverse canonical identity pullback under its derived
adjunction and the identity adjunction. The inverse conjugate is the transpose
of the identity pullback comparison. The derived adjunction factorization and
the identity localization factorization show that this is the right-derived
localization of lowerStarId followed by the canonical right-derived identity
isomorphism. For bounded-below complexes the analogous localization is exactly
d as displayed. The comparison rightDerivedFunctorPlusCompatibility is the
unique comparison respecting the derived units; naturality of right-derived
localization therefore identifies the included d inverse followed by that
comparison with the unbounded inverse conjugate. This is an identity of natural
transformations, so evaluating at any K gives the asserted formula. It involves
no proper/open square and holds for the zero object and the zero ring. -/
theorem identityPush_plus_inclusion
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] (X : Scheme.{u})
    (K : DerivedCategory.Plus
      (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) :
    let d := Functor.rightDerivedFunctorPlusNatIso
      (lowerStarId (ModuleCat.{u + 1} Λ) X) ≪≫
        Functor.rightDerivedFunctorPlusIdIso _
    DerivedCategory.Plus.ι.map (d.inv.app K) ≫
      (lowerStar (ModuleCat.{u + 1} Λ) (𝟙 X)).rightDerivedFunctorPlusCompatibility.hom.app K =
    ((conjugateIsoEquiv
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X))
      Adjunction.id) (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).symm).inv.app K.obj  := by
  let P := upperStar (ModuleCat.{u + 1} Λ) (𝟙 X)
  let R := lowerStar (ModuleCat.{u + 1} Λ) (𝟙 X)
  let a := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)
  let ap := derivedUpperStarLowerStarAdjunctionPlus (ModuleCat.{u + 1} Λ) (𝟙 X)
  let e := Functor.mapDerivedCategoryPlusNatIso
    (upperStarId (ModuleCat.{u + 1} Λ) X) ≪≫ Functor.mapDerivedCategoryPlusIdIso _
  let d := Functor.rightDerivedFunctorPlusNatIso
    (lowerStarId (ModuleCat.{u + 1} Λ) X) ≪≫ Functor.rightDerivedFunctorPlusIdIso _
  have he : DerivedCategory.Plus.ι.map (e.hom.app K) =
      (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} Λ) X) ≪≫
        Functor.mapDerivedCategoryIdIso _).hom.app K.obj := by
    simp only [e, Iso.trans_hom, NatTrans.comp_app, Functor.map_comp,
      Functor.ι_map_mapDerivedCategoryPlusNatIso_hom_app,
      Functor.ι_map_mapDerivedCategoryPlusIdIso_hom_app]
    rfl
  have hu : DerivedCategory.Plus.ι.map (ap.unit.app K) =
      a.unit.app K.obj ≫ R.rightDerivedFunctor.map
        ((leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) (𝟙 X)).hom.app
          K.obj) ≫ R.rightDerivedFunctorPlusCompatibility.inv.app
            (P.mapDerivedCategoryPlus.obj K) := by
    change DerivedCategory.Plus.ι.map
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (𝟙 X)).derivedAdjunctionPlus.unit.app
        K) = _
    rw [Adjunction.derivedAdjunctionPlus, Adjunction.map_restrictFullyFaithful_unit_app]
    simp only [Functor.mapDerivedCategoryPlusCompatibility, Iso.symm_hom,
      Iso.refl_inv, NatTrans.id_app, Adjunction.ofNatIsoLeft_unit, NatTrans.comp_app,
      Functor.whiskerRight_app,
      Category.assoc]
    erw [CategoryTheory.Functor.map_id, Category.id_comp]
    rfl
  dsimp only [P] at hu
  have hn := R.rightDerivedFunctorPlusCompatibility.hom.naturality (e.hom.app K)
  dsimp only [Functor.comp_map, Functor.id_obj] at hn
  change DerivedCategory.Plus.ι.map (d.inv.app K) ≫
    R.rightDerivedFunctorPlusCompatibility.hom.app K = _
  rw [← plus_identity_unit Λ X K, Functor.map_comp, Category.assoc]
  change DerivedCategory.Plus.ι.map (ap.unit.app K) ≫
    DerivedCategory.Plus.ι.map (R.rightDerivedFunctorPlus.map (e.hom.app K)) ≫
      R.rightDerivedFunctorPlusCompatibility.hom.app K = _
  rw [hn, hu]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_app_assoc]
  rw [← Functor.map_comp, he]
  have hl : (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X).hom.app K.obj =
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) (𝟙 X)).hom.app K.obj ≫
        (Functor.mapDerivedCategoryNatIso (upperStarId (ModuleCat.{u + 1} Λ) X) ≪≫
          Functor.mapDerivedCategoryIdIso _).hom.app K.obj := by
    simp only [leftDerivedUpperStarId, Functor.leftDerivedFunctorNatIso,
      Iso.trans_hom, NatTrans.comp_app, Iso.symm_hom, Category.assoc,
      Iso.inv_hom_id_app_assoc]
    rfl
  rw [← hl]
  exact (inverse_identity_conjugate a
    (leftDerivedUpperStarId (ModuleCat.{u + 1} Λ) X) K.obj).symm

end AlgebraicGeometry.ProEtale
