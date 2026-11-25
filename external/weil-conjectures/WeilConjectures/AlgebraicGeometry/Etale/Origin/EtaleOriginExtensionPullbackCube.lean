/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginScalarPullbackData
import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginRestrictionPullbackCube
import all WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteOpenScalarRealizationTransport
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarMateData

/-! # Intrinsic realization and scalar pullback coherence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor Etale.scalarTensorIso Scheme.completedAdicDerivedChange

private theorem mate_whisker_top
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {G G' : C ⥤ E} {H : D ⥤ F}
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (w : TwoSquare G' L₁ L₂ H) (t : G ⟶ G') :
    mateEquiv a₁ a₂ (w.whiskerTop t) = (mateEquiv a₁ a₂ w).whiskerRight t := by
  simpa [TwoSquare.whiskerBottom, TwoSquare.whiskerLeft] using
    mateEquiv_whiskerTop_whiskerBottom a₁ a₂ w t (𝟙 H)

private theorem conjugate_cube
    {D : Type*} [Category D] {X Y Z W U V : D}
    (e : X ≅ Y) (d : X ≅ Z) (q : W ≅ V) (c : U ≅ V)
    (f : Y ⟶ W) (g : Z ⟶ U)
    (h : e.inv ≫ d.hom ≫ g = f ≫ q.hom ≫ c.inv) :
    d.inv ≫ e.hom ≫ f = g ≫ c.hom ≫ q.inv := by
  apply (cancel_epi d.hom).mp
  apply (cancel_mono q.hom).mp
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have h' := congrArg (fun t ↦ e.hom ≫ t ≫ c.hom) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id,
    Category.comp_id] using h'.symm

private theorem realization_scalar_mate
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (mateEquiv
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T)
          (RingHom.ulift.{u + 1, u + 1, u, u} φ)))
      (Scheme.pbcDerivedScalarAdjunction
        (Scheme.FiniteCompactScalar.scalarRingMap φ T))
      (TwoSquare.mk _ _ _ _ (Scheme.FiniteCompactScalar.realizationScalarIso φ T).hom)) =
      (Functor.mapDerivedCategorySquareIso
        (Scheme.sfRealizationRestriction T φ)).inv := by
  apply mateEquiv_eq_of_unit
  intro K
  exact Scheme.FiniteCompactScalar.realization_scalar_unit T φ K

private theorem site_scalar_mate
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (mateEquiv
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars T.smallEtaleTopology
          (RingHom.ulift.{u + 1, u + 1, u, u} φ)))
      (Scheme.pbcDerivedScalarAdjunction
        (Scheme.FiniteCompactScalar.scalarRingMap φ T))
      (TwoSquare.mk _ _ _ _ (Scheme.FiniteCompactScalar.siteScalarIso φ T).hom)) =
      (properOriginRestrictionIso φ T).inv := by
  let a := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars T.smallEtaleTopology (RingHom.ulift.{u + 1, u + 1, u, u} φ))
  let b := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology T) (RingHom.ulift.{u + 1, u + 1, u, u} φ))
  let c := Scheme.pbcDerivedScalarAdjunction
    (Scheme.FiniteCompactScalar.scalarRingMap φ T)
  let s := TwoSquare.mk _ _ _ _
    (pbcComparisonReduction T (RingHom.ulift.{u + 1, u + 1, u, u} φ)).hom
  let r := TwoSquare.mk _ _ _ _ (Scheme.FiniteCompactScalar.realizationScalarIso φ T).hom
  have hs : mateEquiv a b s =
      TwoSquare.mk _ _ _ _
        (pbcDerivedComparisonRestrict T (RingHom.ulift.{u + 1, u + 1, u, u} φ)).inv := by
    exact Equiv.apply_symm_apply _ _
  have hr : mateEquiv b c r = TwoSquare.mk _ _ _ _
      (Functor.mapDerivedCategorySquareIso (Scheme.sfRealizationRestriction T φ)).inv := by
    exact realization_scalar_mate φ T
  have hw : TwoSquare.mk _ _ _ _ (Scheme.FiniteCompactScalar.siteScalarIso φ T).hom =
      ((s.hComp r).whiskerTop
        (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A T).hom).whiskerBottom
          (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso B T).inv := by
    ext K
    simp only [s, r, Scheme.FiniteCompactScalar.siteScalarIso,
      TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
      Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
      Functor.isoWhiskerLeft_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.assoc]
  change (mateEquiv a c _) = _
  rw [hw, mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp a b c, hs, hr]
  ext K
  simp only [properOriginRestrictionIso, TwoSquare.mk, TwoSquare.vComp,
    TwoSquare.whiskerLeft, TwoSquare.whiskerRight, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.assoc]
  rfl

/-- The extension/realization comparison commutes with geometric pullback.
Source: Stacks 0D6D, 06YY and 07A6; extension part of the coefficient comparison
in Tag 0E48 (blueprint: lem-fix-etale-origin-extension-pullback-cube).

Proof: compute the ordinary scalar extension by the balanced tensor product.
The section-normalized site realization and the scalar adjunction comparison send
x tensor b to the same section in either order of inverse image and realization.
For an unbounded input C choose a flat-term K-flat resolution. Inverse image and
derived scalar extension are computed by the ordinary operations on this model.
The ordinary balancing identity in every degree commutes with the differential,
so it gives equality of the comparison chain maps. The representative
normalization of Etale.scalarPullbackIso identifies its component; the intrinsic
scalar-adjunction mate identifies directImageScalarPullbackIso. The normalized
site comparison identifies originPullback through its geometric counit equation.
Cancel the common localized resolution arrows and use naturality to descend the
cube to C. No scalar restriction/tensor identification, projection formula or
boundedness assertion is used. Identity coefficient maps, zero rings and empty
schemes satisfy the same balancing identity. -/
theorem etaleOriginExtensionPullbackCube
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (C : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y) :
    (Scheme.proEtaleConstantRingDerivedPullback B p).map
        ((Scheme.FiniteCompactScalar.siteScalarIso φ Y).inv.app C) ≫
      (directImageScalarPullbackIso φ p).hom.app
        ((finiteCoefficientIntrinsicDerivedComparison Y A).obj C) ≫
      (directImageScalarExtension φ Z).map ((originPullback A p).app C) =
    (originPullback B p).app
        ((Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) Y).obj C) ≫
      (finiteCoefficientIntrinsicDerivedComparison Z B).map
        ((Etale.scalarPullbackIso (RingHom.ulift.{u + 1, u + 1, u, u} φ) p).hom.app C) ≫
      (Scheme.FiniteCompactScalar.siteScalarIso φ Z).inv.app
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).leftDerivedFunctor.obj
          C) := by
  let a := RingHom.ulift.{u + 1, u + 1, u, u} φ
  let ey := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Y.smallEtaleTopology a)
  let ez := Adjunction.ofIsRightAdjoint
    (Sheaf.derivedRestrictScalars Z.smallEtaleTopology a)
  let iy := Scheme.pbcDerivedScalarAdjunction
    (Scheme.FiniteCompactScalar.scalarRingMap φ Y)
  let iz := Scheme.pbcDerivedScalarAdjunction
    (Scheme.FiniteCompactScalar.scalarRingMap φ Z)
  let sy := TwoSquare.mk _ _ _ _ (Scheme.FiniteCompactScalar.siteScalarIso φ Y).hom
  let sz := TwoSquare.mk _ _ _ _ (Scheme.FiniteCompactScalar.siteScalarIso φ Z).hom
  let sp := TwoSquare.mk _ _ _ _ (directImageScalarPullbackIso φ p).inv
  let se := TwoSquare.mk _ _ _ _ (Etale.scalarPullbackIso a p).inv
  have hsy : mateEquiv ey iy sy =
      TwoSquare.mk _ _ _ _ (properOriginRestrictionIso φ Y).inv :=
    site_scalar_mate φ Y
  have hsz : mateEquiv ez iz sz =
      TwoSquare.mk _ _ _ _ (properOriginRestrictionIso φ Z).inv :=
    site_scalar_mate φ Z
  have hsp : mateEquiv iy iz sp =
      TwoSquare.mk _ _ _ _ (originRestrictionPullback φ p) := by
    exact Equiv.apply_symm_apply _ _
  have hse : mateEquiv ey ez se = TwoSquare.mk _ _ _ _
      (Etale.scalarRestrictionPullbackIso a p).hom := by
    dsimp only [se]
    change mateEquiv ey ez (scalarPullbackEtaleIso a p).inv = _
    rw [scalarPullbackEtaleIso_eq_fromMate]
    exact Equiv.apply_symm_apply _ _
  have hm : ((sy.hComp sp).whiskerBottom (originPullback B p)) =
      ((se.hComp sz).whiskerTop (originPullback A p)) := by
    apply (mateEquiv ey iz).injective
    rw [mateEquiv_whiskerBottom, mate_whisker_top,
      mateEquiv_vcomp ey iy iz, mateEquiv_vcomp ey ez iz, hsy, hsp, hse, hsz]
    ext N
    simpa only [a, Scheme.pbcDerivedRestrict, Scheme.pbcRestrict,
      Scheme.FiniteCompactScalar.scalarRingMap, scalarMateRestriction,
      Scheme.proEtaleRingRestrictScalars, TwoSquare.mk, TwoSquare.vComp,
      TwoSquare.whiskerLeft, TwoSquare.whiskerRight,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using
      etaleOriginRestrictionPullbackCube φ p N
  have h := congrArg (fun t ↦ t.app C) hm
  simp only [sy, sp, se, sz, TwoSquare.mk,
    TwoSquare.hComp, TwoSquare.whiskerTop,
    TwoSquare.whiskerBottom, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Category.comp_id,
    Category.assoc] at h
  exact conjugate_cube
    ((directImageScalarPullbackIso φ p).app
      ((finiteCoefficientIntrinsicDerivedComparison Y A).obj C))
    ((Scheme.proEtaleConstantRingDerivedPullback B p).mapIso
      ((Scheme.FiniteCompactScalar.siteScalarIso φ Y).app C))
    ((Scheme.FiniteCompactScalar.siteScalarIso φ Z).app
      ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).leftDerivedFunctor.obj C))
    ((finiteCoefficientIntrinsicDerivedComparison Z B).mapIso
      ((Etale.scalarPullbackIso a p).app C))
    ((directImageScalarExtension φ Z).map ((originPullback A p).app C))
    ((originPullback B p).app ((Etale.scalarExtension a Y).obj C)) h

end AlgebraicGeometry.ProEtale
