/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactScalarCoordinates
import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteOpenScalarSiteTransport
import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteOpenScalarRealizationTransport

/-! # Scalar transport for the open factor of compact support -/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.FiniteCompactScalar

attribute [local irreducible] Functor.mapDerivedCategory Functor.leftAdjoint

private def scalarTranspose
    {C₀ C₁ D₀ D₁ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {Sx : C₀ ⥤ C₁} {Rx : C₁ ⥤ C₀}
    {Sy : D₀ ⥤ D₁} {Ry : D₁ ⥤ D₀}
    (ax : Sx ⊣ Rx) (ay : Sy ⊣ Ry)
    {P₀ : C₀ ⥤ D₀} {P₁ : C₁ ⥤ D₁}
    (r : Rx ⋙ P₀ ⟶ P₁ ⋙ Ry) : P₀ ⋙ Sy ⟶ Sx ⋙ P₁ :=
  ((mateEquiv ax ay).symm (TwoSquare.mk _ _ _ _ r))

private theorem scalarTranspose_app
    {C₀ C₁ D₀ D₁ : Type*}
    [Category C₀] [Category C₁] [Category D₀] [Category D₁]
    {Sx : C₀ ⥤ C₁} {Rx : C₁ ⥤ C₀}
    {Sy : D₀ ⥤ D₁} {Ry : D₁ ⥤ D₀}
    (ax : Sx ⊣ Rx) (ay : Sy ⊣ Ry)
    {P₀ : C₀ ⥤ D₀} {P₁ : C₁ ⥤ D₁}
    (r : Rx ⋙ P₀ ⟶ P₁ ⋙ Ry) (K : C₀) :
    (scalarTranspose ax ay r).app K =
      (ay.homEquiv _ _).symm (P₀.map (ax.unit.app K) ≫ r.app (Sx.obj K)) := by
  apply (ay.homEquiv _ _).injective
  erw [Equiv.apply_symm_apply]
  simpa only [Adjunction.homEquiv_unit, scalarTranspose, TwoSquare.mk,
    Functor.id_obj, Functor.comp_obj] using
    (unit_mateEquiv_symm ax ay (TwoSquare.mk _ _ _ _ r) K).symm

private theorem openScalar_transport_base
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (G : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X) :
    ((pbcDerivedScalarAdjunction (scalarRingMap φ Z)).homEquiv _ _).symm
        ((sfIntrinsicExtensionByZero j A).mapDerivedCategory.map
            ((pbcDerivedScalarAdjunction (scalarRingMap φ X)).unit.app
              ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G)) ≫
          (Functor.mapDerivedCategorySquareIso (sfOpenRestriction j φ)).hom.app
            ((pbcDerivedExtend (scalarRingMap φ X)).obj
              ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G))) ≫
      (sfIntrinsicExtensionByZero j B).mapDerivedCategory.map
        ((siteScalarIso φ X).hom.app G) =
    (pbcDerivedExtend (scalarRingMap φ Z)).map ((openSiteIso A j).inv.app G) ≫
      (siteScalarIso φ Z).hom.app
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.obj G) ≫
      (ProEtale.finiteCoefficientIntrinsicDerivedComparison Z B).map
        ((Etale.FiniteCompactScalar.openScalarIso
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) j).hom.app G) ≫
      (openSiteIso B j).hom.app
        ((Etale.scalarExtension φ.ulift X).obj G) := by
  let α := scalarTranspose
    (pbcDerivedScalarAdjunction (scalarRingMap φ X))
    (pbcDerivedScalarAdjunction (scalarRingMap φ Z))
    (Functor.mapDerivedCategorySquareIso (sfOpenRestriction j φ)).hom
  let C (R : Type u) [CommRing R] (T : Scheme.{u}) :=
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) T).mapDerivedCategory
  let E (R : Type u) [CommRing R] [Finite R] (T : Scheme.{u}) :=
    (sfIntrinsicDerivedEquivalence T R).functor
  let P (R : Type u) [CommRing R] :=
    (ProEtale.openImmersionLowerShriek
      (ModuleCat.{u + 1} (ULift.{u + 1, u} R)) j).mapDerivedCategory
  let I (R : Type u) [CommRing R] [Finite R] :=
    (sfIntrinsicExtensionByZero j R).mapDerivedCategory
  let S := pbcDerivedExtend (scalarRingMap φ Z)
  let β := scalarTranspose
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (ProEt.topology X) φ.ulift))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (ProEt.topology Z) φ.ulift))
    (Functor.mapDerivedCategorySquareIso (sfFixedOpenRestriction j φ)).hom
  have hr := fixedOpenScalar_realization_transport φ j ((C A X).obj G)
  erw [← scalarTranspose_app, ← scalarTranspose_app] at hr
  change α.app ((E A X).obj ((C A X).obj G)) ≫
      (I B).map ((realizationScalarIso φ X).hom.app ((C A X).obj G)) =
    S.map ((openRealizationIso A j).hom.app ((C A X).obj G)) ≫
      (realizationScalarIso φ Z).hom.app ((P A).obj ((C A X).obj G)) ≫
      (E B Z).map (β.app ((C A X).obj G)) ≫
      (openRealizationIso B j).inv.app _ at hr
  have hs := fixedOpenScalar_site_transport φ j G
  erw [← scalarTranspose_app] at hs
  change β.app ((C A X).obj G) ≫
      (P B).map ((ProEtale.pbcComparisonReduction X φ.ulift).hom.app G) = _ at hs
  have hn := α.naturality ((intrinsicSiteFunctorIso A X).hom.app G)
  have hb := (openRealizationIso B j).inv.naturality
    ((ProEtale.pbcComparisonReduction X φ.ulift).hom.app G)
  have hd := (realizationScalarIso φ Z).hom.naturality
    ((Functor.mapDerivedCategorySquareIso
      (ProEtale.openImmersionLowerShriekComparisonUpperStarIso
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)).inv.app G)
  have he := (intrinsicSiteFunctorIso B Z).inv.naturality
    ((Etale.FiniteCompactScalar.openScalarIso φ.ulift j).hom.app G)
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn hb hd he
  erw [← scalarTranspose_app]
  change α.app _ ≫ (I B).map _ = _
  simp only [siteScalarIso, openSiteIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Category.id_comp, Functor.map_comp,
    Category.assoc]
  rw [← reassoc_of% hn, reassoc_of% hr]
  erw [← reassoc_of% hb]
  slice_lhs 4 5 => rw [← Functor.map_comp, hs]
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% hd]
  rw [← reassoc_of% he]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app, Iso.inv_hom_id_app_assoc]
  erw [Category.comp_id]
  dsimp only [C, E, P, I, S]
  simp only [Functor.mapDerivedCategorySquareIso, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_inv, Iso.symm_hom, NatTrans.comp_app, Functor.map_comp, Category.assoc]

/-- The open scalar mate is compatible with the canonical site and realization
comparisons. This assertion involves only extension by zero, with no proper map.

Source: Stacks Tags 03DI, 09AF and 00YV; blueprint compact-support
constructibility proof, Step 5, and the open factor of scalar transport.
(blueprint: lem-finite-open-scalar-transport).

Proof: factor the site/scalar and open/site comparisons through fixed-coefficient
pro-etale comparison and intrinsic realization. Naturality of the intrinsic open
scalar transpose transports intrinsicSiteFunctorIso at the input. Apply
fixedOpenScalar_realization_transport, move the fixed site/scalar comparison
past openRealizationIso by naturality, and apply fixedOpenScalar_site_transport.
Naturality of realizationScalarIso and intrinsicSiteFunctorIso aligns the etale
open scalar map. Cancel the adjacent inverse comparison factors. Finally,
postcompose by extension by zero of the realization of eGB; naturality of
openSiteIso gives the displayed arbitrary output isomorphism. No boundedness,
flatness, nonzero ring, or nonempty scheme is used. -/
theorem openScalar_transport
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j]
    (G : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) X)
    (GB : Etale.DerivedCategoryModule (ULift.{u + 1, u} B) X)
    (eGB : (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj G ≅ GB) :
    ((pbcDerivedScalarAdjunction (scalarRingMap φ Z)).homEquiv _ _).symm
        ((sfIntrinsicExtensionByZero j A).mapDerivedCategory.map
            ((pbcDerivedScalarAdjunction (scalarRingMap φ X)).unit.app
              ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G)) ≫
          (Functor.mapDerivedCategorySquareIso (sfOpenRestriction j φ)).hom.app
            ((pbcDerivedExtend (scalarRingMap φ X)).obj
              ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G))) ≫
      (sfIntrinsicExtensionByZero j B).mapDerivedCategory.map
        ((siteScalarIso φ X).hom.app G ≫
          (ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).map eGB.hom) =
    (pbcDerivedExtend (scalarRingMap φ Z)).map ((openSiteIso A j).inv.app G) ≫
      (siteScalarIso φ Z).hom.app
        ((Etale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory.obj G) ≫
      (ProEtale.finiteCoefficientIntrinsicDerivedComparison Z B).map
        ((Etale.FiniteCompactScalar.openScalarIso
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) j).hom.app G ≫
          (Etale.openImmersionLowerShriek
            (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) j).mapDerivedCategory.map eGB.hom) ≫
      (openSiteIso B j).hom.app GB := by
  have h := openScalar_transport_base φ j G
  simp only [Functor.map_comp, Category.assoc] at h ⊢
  erw [reassoc_of% h]
  have hn := (openSiteIso B j).hom.naturality eGB.hom
  dsimp only [Functor.comp_map, Functor.comp_obj] at hn
  rw [← hn]

end AlgebraicGeometry.Scheme.FiniteCompactScalar
