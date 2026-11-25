/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ContinuousScalarFinitePresentation
public import WeilConjectures.AlgebraicGeometry.IntegralCompletedCoefficientTransport
public import WeilConjectures.AlgebraicGeometry.IntegralCriterionReductions
public import WeilConjectures.AlgebraicGeometry.IntegralStratifiedPerfectModels
import WeilConjectures.AlgebraicGeometry.ContinuousCoefficientModuleEncoding
import all WeilConjectures.AlgebraicGeometry.FiniteDiscreteOrdinaryEncoding
import all WeilConjectures.AlgebraicGeometry.IntegralConstantSectionProjection
import all WeilConjectures.AlgebraicGeometry.IntegralModelsFlatResidue
import all WeilConjectures.AlgebraicGeometry.WeilCompletedRealizationRegular
import all WeilConjectures.SixFunctors.ProEtale.IntegralNormalizedRestrictionSquares

/-! The scalar-endomorphism part of the regular integral comparison.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3).
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.IntegralSectionScalars
attribute [local irreducible] upperStarFromPoint CondensedRing.upperStar
  integralSectionFunctor Scheme.integralDetailedCoefficientComparison
  Scheme.proEtaleModuleInverseImage Scheme.integralConstantModule

open MonoidalCategory
attribute [local instance] AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify
  Scheme.ProEt.instHasSheafifyTopologyAb_weilConjectures
  IntegralModelsStacks.projectionAbLocallyBijective
  WeilConjectures.instEssentiallySmallProEt_weilConjectures

private def liftedRegularIso (A : Type u) [CommRing A] :
    (FiniteConstantModel.scalarModules A).obj (ModuleCat.of A (ULift.{u + 1} A)) ≅
      Mod.regular (AddCommGrpCat.of (ULift.{u + 1} A)) := by
  refine Mod.isoMk (Iso.refl _) ?_
  apply AddCommGrpCat.hom_ext_toIntLinearMap
  apply TensorProduct.ext'
  intro a b
  rfl

private def constantRegularIso (A : Type u) [CommRing A] :
    ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
      (AddCommGrpCat.of (ULift.{u + 1} A))).obj
        ((FiniteConstantModel.scalarModules A).obj (ModuleCat.of A (ULift.{u + 1} A))) ≅
      Mod.regular ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} A))) :=
  ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
    (AddCommGrpCat.of (ULift.{u + 1} A))).mapIso (liftedRegularIso A) ≪≫
      Mod.isoMk (Iso.refl _) (by simp)

private def continuousRegularIso (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    (continuousScalarFunctor A).obj (ModuleCat.of A (ULift.{u + 1} A)) ≅
      Mod.regular (Profinite.continuousCoefficientRingObj A) := by
  unfold continuousScalarFunctor
  exact (Mod.extendScalars (FiniteConstantModel.scalarToContinuous A)).mapIso
    (constantRegularIso A) ≪≫ Mod.regularExtensionIso (FiniteConstantModel.scalarToContinuous A)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem continuousRegularIso_unit (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    Mod.extendUnitHom (FiniteConstantModel.scalarToContinuous A)
      (((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
        (AddCommGrpCat.of (ULift.{u + 1} A))).obj
          ((FiniteConstantModel.scalarModules A).obj (ModuleCat.of A (ULift.{u + 1} A)))) ≫
      (continuousRegularIso A).hom.hom = FiniteConstantModel.scalarToContinuous A := by
  let φ := FiniteConstantModel.scalarToContinuous A
  have h := congrArg Mod.Hom.hom
    ((Mod.extendRestrictAdjunction φ).unit.naturality (constantRegularIso A).hom)
  change (constantRegularIso A).hom.hom ≫ Mod.extendUnitHom φ _ =
    Mod.extendUnitHom φ _ ≫ ((Mod.extendScalars φ).map (constantRegularIso A).hom).hom at h
  dsimp only [continuousRegularIso, id, Iso.trans_hom, Functor.mapIso_hom, Mod.comp_hom']
  rw [← Category.assoc, ← h, Category.assoc]
  change (constantRegularIso A).hom.hom ≫
    (Mod.extendUnitHom φ _ ≫ (Mod.extendHom φ (Mod.regularCoefficientMap φ)).hom) = φ
  rw [Mod.extendUnitHom_extendHom]
  change (constantRegularIso A).hom.hom ≫ φ = φ
  change ((constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map (𝟙 _) ≫ 𝟙 _) ≫ φ = φ
  change (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
    (𝟙 (AddCommGrpCat.of (ULift.{u + 1} A))) ≫ φ = φ
  rw [CategoryTheory.Functor.map_id, Category.id_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem continuousRegularIso_coefficient (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A]
    (f : ModuleCat.of A (ULift.{u + 1} A) ⟶ ModuleCat.of A (ULift.{u + 1} A)) :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
      ((FiniteConstantModel.scalarModules A).map f).hom ≫
        FiniteConstantModel.scalarToContinuous A =
      FiniteConstantModel.scalarToContinuous A ≫
        ((continuousRegularIso A).inv ≫ (continuousScalarFunctor A).map f ≫
          (continuousRegularIso A).hom).hom := by
  let P := (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMod
    (AddCommGrpCat.of (ULift.{u + 1} A))
  let φ := FiniteConstantModel.scalarToContinuous A
  let p := P.map ((FiniteConstantModel.scalarModules A).map f)
  have h := congrArg Mod.Hom.hom ((Mod.extendRestrictAdjunction φ).unit.naturality p)
  change p.hom ≫ Mod.extendUnitHom φ _ =
    Mod.extendUnitHom φ _ ≫ ((Mod.extendScalars φ).map p).hom at h
  have h' := congrArg (fun z ↦ z ≫ (continuousRegularIso A).hom.hom) h
  simp only [Category.assoc] at h'
  rw [continuousRegularIso_unit] at h'
  have he := congrArg Mod.Hom.hom (continuousRegularIso A).hom_inv_id
  change (continuousRegularIso A).hom.hom ≫ (continuousRegularIso A).inv.hom = 𝟙 _ at he
  calc
    p.hom ≫ φ = _ := h'
    _ = (Mod.extendUnitHom φ _ ≫ (continuousRegularIso A).hom.hom) ≫
        ((continuousRegularIso A).inv ≫ (continuousScalarFunctor A).map f ≫
          (continuousRegularIso A).hom).hom := by
      simp only [Mod.comp_hom', Category.assoc]
      rw [← Category.assoc (continuousRegularIso A).hom.hom
        (continuousRegularIso A).inv.hom, he, Category.id_comp]
      rfl
    _ = _ := by rw [continuousRegularIso_unit]

attribute [local irreducible] continuousScalarFunctor

private def pulledRegularIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ((letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
      continuousScalarFunctor (Padic.coefficientExtensionIntegers l E)) ⋙
      (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E)).obj
        (ModuleCat.of (Padic.coefficientExtensionIntegers l E)
          (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) ≅
      Mod.regular (AdicCompletion.ring l E X) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  exact ((upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E)).mapIso
    (continuousRegularIso (Padic.coefficientExtensionIntegers l E)) ≪≫
      Mod.isoMk (Iso.refl _) (by simp)

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
private theorem pulledRegularIso_coefficient (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u})
    (f : ModuleCat.of (Padic.coefficientExtensionIntegers l E)
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E)) ⟶
      ModuleCat.of (Padic.coefficientExtensionIntegers l E)
        (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))) :
    let : EssentiallySmall.{u + 1} X.ProEt :=
      WeilConjectures.instEssentiallySmallProEt_weilConjectures X
    let : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
      Scheme.ProEt.instHasSheafifyTopologyAb_weilConjectures X
    let : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
      AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify X
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let A : Type u := Padic.coefficientExtensionIntegers l E
    let L := continuousScalarFunctor A ⋙
      (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E)
    FiniteDiscreteOrdinary.canonicalAbelianMap.{u} A X ≫
        ((pulledRegularIso l E X).inv ≫ L.map f ≫ (pulledRegularIso l E X).hom).hom =
      (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).map
        ((FiniteConstantModel.scalarModules A).map f).hom ≫
          FiniteDiscreteOrdinary.canonicalAbelianMap.{u} A X := by
  let : EssentiallySmall.{u + 1} X.ProEt :=
    WeilConjectures.instEssentiallySmallProEt_weilConjectures X
  let : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
    Scheme.ProEt.instHasSheafifyTopologyAb_weilConjectures X
  let : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
    AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify X
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A : Type u := Padic.coefficientExtensionIntegers l E
  let P := upperStarFromPoint X
  have hc := continuousRegularIso_coefficient A f
  have hn := (constantSchemeIso X).hom.naturality
    ((FiniteConstantModel.scalarModules A).map f).hom
  have hq :
      ((pulledRegularIso l E X).inv ≫
          (continuousScalarFunctor A ⋙ P.mapMod (DerivedNakayama.integerRing l E)).map f ≫
            (pulledRegularIso l E X).hom).hom =
        P.map (((continuousRegularIso A).inv ≫ (continuousScalarFunctor A).map f ≫
          (continuousRegularIso A).hom).hom) := by
    change (𝟙 _ ≫ P.map (continuousRegularIso A).inv.hom) ≫
      P.map ((continuousScalarFunctor A).map f).hom ≫
        (P.map (continuousRegularIso A).hom.hom ≫ 𝟙 _) = _
    simp only [Category.id_comp, Category.comp_id, Mod.comp_hom', P.map_comp]
  dsimp only
  erw [hq]
  change (constantSchemeIso X).hom.app _ ≫ P.map (FiniteConstantModel.scalarToContinuous A) ≫
      P.map _ = _
  rw [← P.map_comp, ← hc, P.map_comp, ← Category.assoc]
  exact congrArg (fun z ↦ z ≫ P.map (FiniteConstantModel.scalarToContinuous A)) hn.symm

private def scalarEndo (A : Type u) [CommRing A] (a : A) :
    ModuleCat.of A (ULift.{u + 1} A) ⟶ ModuleCat.of A (ULift.{u + 1} A) :=
  ModuleCat.ofHom ((ULift.moduleEquiv (R := A) (M := A)).symm.toLinearMap.comp
    ((LinearMap.mulLeft A a).comp (ULift.moduleEquiv (R := A) (M := A)).toLinearMap))

set_option backward.isDefEq.respectTransparency false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
private theorem pulledRegularIso_scalar_one (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (a : Padic.coefficientExtensionIntegers l E) (U : X.ProEtᵒᵖ) :
    let : EssentiallySmall.{u + 1} X.ProEt :=
      WeilConjectures.instEssentiallySmallProEt_weilConjectures X
    let : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
      Scheme.ProEt.instHasSheafifyTopologyAb_weilConjectures X
    let : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
      AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify X
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let A : Type u := Padic.coefficientExtensionIntegers l E
    let L := continuousScalarFunctor A ⋙
      (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E)
    (((pulledRegularIso l E X).inv ≫ L.map (scalarEndo A a) ≫
        (pulledRegularIso l E X).hom).hom).hom.app U
          (1 : (FiniteDiscreteOrdinary.sectionRing A X).obj.obj U) =
      (FiniteDiscreteOrdinary.canonicalRingMap.{u} A X).hom.app U
        ((toSheafify (Scheme.ProEt.topology X)
          ((Functor.const X.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1} A)))).app U
            (ULift.up a)) := by
  let : EssentiallySmall.{u + 1} X.ProEt :=
    WeilConjectures.instEssentiallySmallProEt_weilConjectures X
  let : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
    Scheme.ProEt.instHasSheafifyTopologyAb_weilConjectures X
  let : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
    AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify X
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A : Type u := Padic.coefficientExtensionIntegers l E
  let J : GrothendieckTopology X.ProEt := Scheme.ProEt.topology X
  let η := toSheafify J
    ((Functor.const X.ProEtᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))
  let c := FiniteDiscreteOrdinary.canonicalAbelianMap.{u} A X
  have hc (b : ULift.{u + 1} A) :=
    FiniteDiscreteOrdinary.canonicalRingMap_normalization.{u} A X U b
  have hc1 : c.hom.app U (η.app U (ULift.up 1)) =
      (1 : (FiniteDiscreteOrdinary.sectionRing A X).obj.obj U) := by
    rw [← hc]
    change (FiniteDiscreteOrdinary.canonicalRingMap.{u} A X).hom.app U
      ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
        (CommRingCat.of (ULift.{u + 1} A)))).app U 1) = _
    simp only [map_one]
  have h := pulledRegularIso_coefficient l E X (scalarEndo A a)
  have h' := congrArg (fun z ↦ z.hom.app U (η.app U (ULift.up 1))) h
  let L := continuousScalarFunctor A ⋙
    (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E)
  let q := ((pulledRegularIso l E X).inv ≫ L.map (scalarEndo A a) ≫
    (pulledRegularIso l E X).hom).hom
  change q.hom.app U (c.hom.app U (η.app U (ULift.up 1))) =
    c.hom.app U (((constantSheaf J Ab.{u + 1}).map
      ((FiniteConstantModel.scalarModules A).map (scalarEndo A a)).hom).hom.app U
        (η.app U (ULift.up 1))) at h'
  rw [hc1] at h'
  have hn := congrArg (fun z ↦ z.app U (ULift.up (1 : A)))
    (toSheafify_naturality J ((Functor.const X.ProEtᵒᵖ).map
      ((FiniteConstantModel.scalarModules A).map (scalarEndo A a)).hom))
  change η.app U (ULift.up (a * 1)) =
    (((constantSheaf J Ab.{u + 1}).map
      ((FiniteConstantModel.scalarModules A).map (scalarEndo A a)).hom).hom.app U
        (η.app U (ULift.up 1))) at hn
  rw [mul_one] at hn
  rw [← hn, ← hc] at h'
  exact h'

private def restrictionUnitIso (X : Scheme.{u})
    {R S : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}} (e : S ≅ R) :
    (SheafOfModules.restrictScalars.{u + 1} e.hom).obj (SheafOfModules.unit R) ≅
      SheafOfModules.unit S := by
  apply (SheafOfModules.fullyFaithfulForget _).preimageIso
  refine PresheafOfModules.isoMk (fun U ↦ ?_) ?_
  · let eU := ((sheafToPresheaf (Scheme.ProEt.topology X) RingCat).mapIso e).app U
    exact ModuleCat.restrictScalarsIsoOfEquiv eU.ringCatIsoToRingEquiv
  · intro U V f
    ext x
    exact ConcreteCategory.congr_hom (e.inv.hom.naturality f) x

private def sectionRegularIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    (integralSectionFunctor l E X ⋙
      SheafOfModules.restrictScalars.{u + 1}
        (Scheme.integralDetailedCoefficientComparison X l E).hom).obj
          (Mod.regular (AdicCompletion.ring l E X)) ≅
      SheafOfModules.unit ((Scheme.adicLisseForget X).obj
        (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))) := by
  let V := sheafCompose (Scheme.ProEt.topology X)
    (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
  let d := V.mapIso (integralSectionRingIso l E X)
  unfold integralSectionFunctor
  exact (SheafOfModules.restrictScalars
    (Scheme.integralDetailedCoefficientComparison X l E).hom).mapIso
      ((SheafOfModules.restrictScalars d.inv).mapIso
        (CondensedRing.sectionModuleRegularIso X (AdicCompletion.ring l E X)) ≪≫
          restrictionUnitIso X d.symm) ≪≫
    restrictionUnitIso X (Scheme.integralDetailedCoefficientComparison X l E)

private def completedRegularIso (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) :
    (Scheme.integralConstantModule X d).obj (ModuleCat.of A A) ≅
      SheafOfModules.unit ((Scheme.adicLisseForget X).obj (Scheme.pbcAdicCompletion X d)) := by
  let dd : Scheme.ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  have := Scheme.completedOne_isIso X dd
  unfold Scheme.integralConstantModule
  exact (Scheme.pbcRestrict (Scheme.pbcCompletedComparison X d).inv).mapIso
    (asIso (Scheme.completedKoszulOne X dd)).symm ≪≫
      restrictionUnitIso X ((Scheme.adicLisseForget X).mapIso
        (Scheme.pbcCompletedComparison X d)).symm

private abbrev sourceRegular (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :=
  ModuleCat.of (Padic.coefficientExtensionIntegers l E)
    (ULift.{u + 1} (Padic.coefficientExtensionIntegers l E))

private def completedInputIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+*
        Padic.coefficientExtensionIntegers l E).toRingHom).obj (sourceRegular l E) ≅
      ModuleCat.of (Scheme.PbcIntegralRing l E) (Scheme.PbcIntegralRing l E) :=
  (LinearEquiv.refl (Scheme.PbcIntegralRing l E) (Scheme.PbcIntegralRing l E)).toModuleIso

private def sectionValueIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    ((letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
      continuousScalarFunctor (Padic.coefficientExtensionIntegers l E)) ⋙
      (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E) ⋙
      integralSectionFunctor l E X ⋙
      SheafOfModules.restrictScalars.{u + 1}
        (Scheme.integralDetailedCoefficientComparison X l E).hom).obj (sourceRegular l E) ≅
      SheafOfModules.unit ((Scheme.adicLisseForget X).obj
        (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))) :=
  (integralSectionFunctor l E X ⋙
    SheafOfModules.restrictScalars.{u + 1}
      (Scheme.integralDetailedCoefficientComparison X l E).hom).mapIso
        (pulledRegularIso l E X) ≪≫ sectionRegularIso l E X

private def constantValueIso (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    (ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+*
        Padic.coefficientExtensionIntegers l E).toRingHom ⋙
      Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)).obj
        (sourceRegular l E) ≅
      SheafOfModules.unit ((Scheme.adicLisseForget X).obj
        (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E))) :=
  (Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)).mapIso
    (completedInputIso l E) ≪≫ completedRegularIso X (Scheme.pbcIntegralDatum l E)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem sectionValueIso_scalar (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (a : Padic.coefficientExtensionIntegers l E) (U : X.ProEtᵒᵖ) :
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let A : Type u := Padic.coefficientExtensionIntegers l E
    let F := continuousScalarFunctor A ⋙
      (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E) ⋙
      integralSectionFunctor l E X ⋙ SheafOfModules.restrictScalars.{u + 1}
        (Scheme.integralDetailedCoefficientComparison X l E).hom
    ((sectionValueIso l E X).inv ≫ F.map (scalarEndo A a) ≫
      (sectionValueIso l E X).hom).val.app U
        (1 : (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)).obj.obj U) =
      (Scheme.integralDetailedCoefficientComparison X l E).inv.hom.app U
        ((integralSectionRingIso l E X).hom.hom.app U
          ((FiniteDiscreteOrdinary.canonicalRingMap.{u} A X).hom.app U
            ((Scheme.adicLisseConstantUnit X (ULift.{u + 1} A)).app U (ULift.up a)))) := by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A : Type u := Padic.coefficientExtensionIntegers l E
  let L := continuousScalarFunctor A ⋙
    (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E)
  unfold sectionValueIso sectionRegularIso integralSectionFunctor
  let q := ((pulledRegularIso l E X).inv ≫ L.map (scalarEndo A a) ≫
    (pulledRegularIso l E X).hom).hom
  change (Scheme.integralDetailedCoefficientComparison X l E).inv.hom.app U
    ((integralSectionRingIso l E X).hom.hom.app U
      (q.hom.app U ((integralSectionRingIso l E X).inv.hom.app U
        ((Scheme.integralDetailedCoefficientComparison X l E).hom.hom.app U 1)))) = _
  rw [map_one, map_one, pulledRegularIso_scalar_one]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem completedRegularIso_scalar (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : Scheme.AdicCoefficientDatum A) (a : A) (U : X.ProEtᵒᵖ) :
    let dd : Scheme.ProEtaleAdicCoefficientDatum A :=
      { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
        quotientFinite := d.quotientFinite }
    ((completedRegularIso X d).inv ≫ (Scheme.integralConstantModule X d).map
      (ModuleCat.ofHom (LinearMap.mul A A a)) ≫ (completedRegularIso X d).hom).val.app U
        (1 : (Scheme.pbcAdicCompletion X d).obj.obj U) =
      (Scheme.pbcCompletedComparison X d).hom.hom.app U
        ((Scheme.adicDatumScalar X dd).hom.app U ((Scheme.adicLisseConstantUnit X A).app U a)) :=
    by
  let dd : Scheme.ProEtaleAdicCoefficientDatum A :=
    { toCompleteCoefficientDatum := d.toCompleteCoefficientDatum
      quotientFinite := d.quotientFinite }
  have := Scheme.completedOne_isIso X dd
  let k := asIso (Scheme.completedKoszulOne X dd)
  unfold completedRegularIso Scheme.integralConstantModule
  change (Scheme.pbcCompletedComparison X d).hom.hom.app U
    (k.inv.val.app U (((Scheme.completedKoszulConstant X dd).map
      (ModuleCat.ofHom (LinearMap.mul A A a))).val.app U
        (k.hom.val.app U ((Scheme.pbcCompletedComparison X d).inv.hom.app U 1)))) = _
  rw [map_one]
  erw [Scheme.completedOne_scalar X dd a U]
  rw [map_smul]
  have hk := congrArg (fun f ↦ f.val.app U (1 : (Scheme.adicDatumRing X dd).obj.obj U))
    k.hom_inv_id
  change k.inv.val.app U ((Scheme.completedKoszulOne X dd).val.app U
    (1 : (Scheme.adicDatumRing X dd).obj.obj U)) =
      (1 : (Scheme.adicDatumRing X dd).obj.obj U) at hk
  erw [hk]
  change (Scheme.pbcCompletedComparison X d).hom.hom.app U (_ * 1) = _
  rw [mul_one]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem constantValueIso_scalar (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (a : Padic.coefficientExtensionIntegers l E) (U : X.ProEtᵒᵖ) :
    let dd : Scheme.ProEtaleAdicCoefficientDatum (Scheme.PbcIntegralRing l E) :=
      { toCompleteCoefficientDatum := (Scheme.pbcIntegralDatum l E).toCompleteCoefficientDatum
        quotientFinite := (Scheme.pbcIntegralDatum l E).quotientFinite }
    let G := ModuleCat.restrictScalars.{u + 1}
      (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+*
        Padic.coefficientExtensionIntegers l E).toRingHom ⋙
      Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)
    ((constantValueIso l E X).inv ≫
      G.map (scalarEndo (Padic.coefficientExtensionIntegers l E) a) ≫
        (constantValueIso l E X).hom).val.app U
          (1 : (Scheme.pbcAdicCompletion X (Scheme.pbcIntegralDatum l E)).obj.obj U) =
      (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)).hom.hom.app U
        ((Scheme.adicDatumScalar X dd).hom.app U
          ((Scheme.adicLisseConstantUnit X (Scheme.PbcIntegralRing l E)).app U (ULift.up a))) :=
    by
  let A : Type u := Padic.coefficientExtensionIntegers l E
  let d := Scheme.pbcIntegralDatum l E
  let G := Scheme.integralConstantModule X d
  let H := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+* A).toRingHom
  have h : (completedInputIso l E).inv ≫ H.map (scalarEndo A a) ≫
      (completedInputIso l E).hom =
    ModuleCat.ofHom (LinearMap.mul (Scheme.PbcIntegralRing l E)
      (Scheme.PbcIntegralRing l E) (ULift.up a)) := by
    rfl
  have he : (constantValueIso l E X).inv ≫ (H ⋙ G).map (scalarEndo A a) ≫
      (constantValueIso l E X).hom =
    (completedRegularIso X d).inv ≫
      G.map (ModuleCat.ofHom (LinearMap.mul (Scheme.PbcIntegralRing l E)
        (Scheme.PbcIntegralRing l E) (ULift.up a))) ≫ (completedRegularIso X d).hom := by
    dsimp only [constantValueIso, Iso.trans_inv, Iso.trans_hom, Functor.mapIso_inv,
      Functor.mapIso_hom, Functor.comp_map]
    change (completedRegularIso X d).inv ≫ G.map (completedInputIso l E).inv ≫
      G.map (H.map (scalarEndo A a)) ≫ G.map (completedInputIso l E).hom ≫
        (completedRegularIso X d).hom = _
    rw [← G.map_comp_assoc, ← G.map_comp_assoc, Category.assoc, h]
  dsimp only
  change (((constantValueIso l E X).inv ≫ (H ⋙ G).map (scalarEndo A a) ≫
    (constantValueIso l E X).hom).val.app U) _ = _
  erw [he]
  exact completedRegularIso_scalar X d (ULift.up a) U

private theorem scalarToContinuous_unit (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] :
    toSheafify (coherentTopology Profinite.{u})
        ((Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A))) ≫
      (FiniteConstantModel.scalarToContinuous A).hom =
        FiniteConstantModel.constantFunctions A := by
  exact Equiv.apply_symm_apply
    ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv
      ((Functor.const Profinite.{u}ᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} A)))
      (Profinite.continuousCoefficientRingObj A))
    (FiniteConstantModel.constantFunctions A)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem scalarToContinuous_pointComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E] :
    (letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
     FiniteConstantModel.scalarToContinuous (Padic.coefficientExtensionIntegers l E)) ≫
      (IntegralConstantModel.pointComparison l E).hom.hom =
    (letI := spectralNorm.normedField (Padic l) E
     FiniteConstantModel.scalarToContinuous (Padic.coefficientExtensionIntegers l E)) := by
  rw [IntegralModelsStacks.pointComparison_eq]
  apply Sheaf.hom_ext
  apply sheafify_hom_ext (coherentTopology Profinite.{u}) _ _
    (sfbCondensedIntegers l E).X.property
  change _ ≫ (_ ≫ _) = _ ≫ _
  rw [← Category.assoc]
  rw [scalarToContinuous_unit, scalarToContinuous_unit]
  ext S a
  rfl

private theorem canonicalAbelianMap_pointComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    (letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
     FiniteDiscreteOrdinary.canonicalAbelianMap.{u} (Padic.coefficientExtensionIntegers l E) X) ≫
      (upperStarFromPoint X).map (IntegralConstantModel.pointComparison l E).hom.hom =
    (IntegralModelsStacks.discreteCoefficientAbelianIso X
      (Padic.coefficientExtensionIntegers l E)).hom ≫ IntegralModelsStacks.scalarMap l E X := by
  let A : Type u := Padic.coefficientExtensionIntegers l E
  let P := upperStarFromPoint X
  have hd := (letI := spectralNorm.normedField (Padic l) E
    IntegralModelsStacks.pointConstantAbIso_scalar A)
  have hp := scalarToContinuous_pointComparison l E
  let φ := (letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    FiniteConstantModel.scalarToContinuous A)
  let j := (IntegralModelsStacks.pointConstantAbIso A).hom
  let ψ := (letI := spectralNorm.normedField (Padic l) E
    (sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map (IntegralModelsStacks.constantToContinuous A))
  let C := (constantSchemeIso X).hom.app (AddCommGrpCat.of (ULift.{u + 1} A))
  change (C ≫ P.map φ) ≫ P.map (IntegralConstantModel.pointComparison l E).hom.hom =
    (C ≫ P.map j) ≫ P.map ψ
  calc
    _ = C ≫ P.map (φ ≫ (IntegralConstantModel.pointComparison l E).hom.hom) := by
      rw [P.map_comp, Category.assoc]
    _ = C ≫ P.map (j ≫ ψ) := congrArg (fun z ↦ C ≫ P.map z) (hp.trans hd.symm)
    _ = _ := by rw [P.map_comp, Category.assoc]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
  WeilConjectures.integralCoefficientAbSheafify WeilConjectures.integralCoefficientRingSheafify
  WeilConjectures.integralCoefficientAbLocallyBijective
  WeilConjectures.integralReductionSiteEssentiallySmall
  WeilConjectures.integralOperationsSiteSmall in
private theorem coefficientRingCompatibility (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    let : EssentiallySmall.{u + 1} X.ProEt :=
      WeilConjectures.instEssentiallySmallProEt_weilConjectures X
    let : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
      Scheme.ProEt.instHasSheafifyTopologyAb_weilConjectures X
    let : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
      AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify X
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let dd : Scheme.ProEtaleAdicCoefficientDatum (Scheme.PbcIntegralRing l E) :=
      { toCompleteCoefficientDatum := (Scheme.pbcIntegralDatum l E).toCompleteCoefficientDatum
        quotientFinite := (Scheme.pbcIntegralDatum l E).quotientFinite }
    FiniteDiscreteOrdinary.canonicalRingMap.{u} (Padic.coefficientExtensionIntegers l E) X ≫
        (integralSectionRingIso l E X).hom ≫ (WeilConjectures.purCoefficientIso l E X).inv =
      Scheme.adicDatumScalar X dd ≫ (Scheme.pbcCompletedComparison X
        (Scheme.pbcIntegralDatum l E)).hom := by
  let : EssentiallySmall.{u + 1} X.ProEt :=
    WeilConjectures.instEssentiallySmallProEt_weilConjectures X
  let : HasSheafify (Scheme.ProEt.topology X) Ab.{u + 1} :=
    Scheme.ProEt.instHasSheafifyTopologyAb_weilConjectures X
  let : HasSheafify (Scheme.ProEt.topology X) CommRingCat.{u + 1} :=
    AlgebraicGeometry.ProEtale.VaryingRing.ringSheafify X
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  let A : Type u := Padic.coefficientExtensionIntegers l E
  let J : GrothendieckTopology X.ProEt := Scheme.ProEt.topology X
  let dd : Scheme.ProEtaleAdicCoefficientDatum (Scheme.PbcIntegralRing l E) :=
    { toCompleteCoefficientDatum := (Scheme.pbcIntegralDatum l E).toCompleteCoefficientDatum
      quotientFinite := (Scheme.pbcIntegralDatum l E).quotientFinite }
  obtain ⟨c, _, _⟩ := IntegralModelsStacks.integral_constant_section_projection l E X
  have hc : c.integers.hom ≫ IntegralModelsStacks.sectionMap X
        (IntegralModelsStacks.scalarMap l E X) ≫
          (IntegralModelsStacks.completedSectionIso l E X).inv =
      Scheme.adicDatumScalar X dd := by
    apply limit.hom_ext
    intro n
    exact (c.projection n.unop).trans
      ((Scheme.adicDatumScalar_exists X dd).exists.choose_spec n.unop).symm
  have ha : FiniteDiscreteOrdinary.canonicalRingMap.{u} A X ≫
      (IntegralModelsStacks.pointSectionIso l E X).hom =
        c.integers.hom ≫ IntegralModelsStacks.sectionMap X
          (IntegralModelsStacks.scalarMap l E X) := by
    apply Sheaf.hom_ext
    apply sheafify_hom_ext J _ _
      (InternalAbelianSheafModule.sectionRingSheaf J
        (condensedRingObj (IntegralModelsStacks.integersObj l E) X)).property
    ext U a
    change (IntegralModelsStacks.pointSectionIso l E X).hom.hom.app U
      ((FiniteDiscreteOrdinary.canonicalRingMap.{u} A X).hom.app U
        ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
          (CommRingCat.of (ULift.{u + 1} A)))).app U a)) =
      (IntegralModelsStacks.scalarMap l E X).hom.app U
        (c.integers.hom.hom.app U
          ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
            (CommRingCat.of (ULift.{u + 1} A)))).app U a))
    rw [FiniteDiscreteOrdinary.canonicalRingMap_normalization, c.integers_normalized]
    exact congrArg (fun z ↦ z.hom.app U
      ((toSheafify J ((Functor.const X.ProEtᵒᵖ).obj
        (AddCommGrpCat.of (ULift.{u + 1} A)))).app U a))
      (canonicalAbelianMap_pointComparison l E X)
  have hc' := congrArg (fun z ↦ z ≫
    (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)).hom) hc
  dsimp only [IntegralModelsStacks.completedSectionIso, Iso.trans_inv, Iso.symm_inv] at hc'
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id] at hc'
  rw [← Category.assoc c.integers.hom (IntegralModelsStacks.sectionMap X
    (IntegralModelsStacks.scalarMap l E X))] at hc'
  rw [← ha] at hc'
  simpa only [Category.assoc, Iso.hom_inv_id_assoc] using hc'

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coefficientScalarCompatibility (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (a : Padic.coefficientExtensionIntegers l E) (U : X.ProEtᵒᵖ) :
    let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
    let A : Type u := Padic.coefficientExtensionIntegers l E
    let dd : Scheme.ProEtaleAdicCoefficientDatum (Scheme.PbcIntegralRing l E) :=
      { toCompleteCoefficientDatum := (Scheme.pbcIntegralDatum l E).toCompleteCoefficientDatum
        quotientFinite := (Scheme.pbcIntegralDatum l E).quotientFinite }
    (Scheme.integralDetailedCoefficientComparison X l E).inv.hom.app U
      ((integralSectionRingIso l E X).hom.hom.app U
        ((FiniteDiscreteOrdinary.canonicalRingMap.{u} A X).hom.app U
          ((Scheme.adicLisseConstantUnit X (ULift.{u + 1} A)).app U (ULift.up a)))) =
      (Scheme.pbcCompletedComparison X (Scheme.pbcIntegralDatum l E)).hom.hom.app U
        ((Scheme.adicDatumScalar X dd).hom.app U
          ((Scheme.adicLisseConstantUnit X (Scheme.PbcIntegralRing l E)).app U (ULift.up a))) :=
    by
  let := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
  have h := congrArg (fun z ↦ z.hom.app U
    ((Scheme.adicLisseConstantUnit X (Scheme.PbcIntegralRing l E)).app U (ULift.up a)))
      (coefficientRingCompatibility l E X)
  have hi := congrArg Iso.inv
    (WeilConjectures.purCoefficientIso_existsUnique l E X).exists.choose_spec
  have hi' := congrArg (fun z ↦ z.hom.app U
    ((integralSectionRingIso l E X).hom.hom.app U
      ((FiniteDiscreteOrdinary.canonicalRingMap.{u}
        (Padic.coefficientExtensionIntegers l E) X).hom.app U
          ((Scheme.adicLisseConstantUnit X (Scheme.PbcIntegralRing l E)).app U (ULift.up a))))) hi
  exact hi'.symm.trans h

/--
The two fixed scalar realizations agree on the lifted regular module and on every
endomorphism given by multiplication by a scalar. This is the rank-one coefficient
calculation: the normalized section-ring and completed-coefficient projections agree
on the scalar section, and the completion projections are jointly monic.

Source: Bhatt--Scholze, Definition 6.8.10 and Proposition 6.8.11(3), the regular
scalar calculation in the integral constructibility bridge.
Proof: identify both regular values with the sectionwise unit module using the
constant-sheaf, scalar-extension, point-pullback, section-action, and coefficient
restriction unit maps. For a scalar `a`, naturality of each unit map identifies its
image with multiplication by the corresponding constant section. The fixed
projection formulas agree at every positive quotient, hence the completion
projections identify the two maps. The zero scalar and empty scheme are included.
(auxiliary; not a blueprint node).
-/
theorem scalarComparison (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) :
    let A := Padic.coefficientExtensionIntegers l E
    let R := ModuleCat.of A (ULift.{u + 1} A)
    let F :=
      (letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
       continuousScalarFunctor A) ⋙
        (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E) ⋙
        integralSectionFunctor l E X ⋙
        SheafOfModules.restrictScalars.{u + 1}
          (Scheme.integralDetailedCoefficientComparison X l E).hom
    let G :=
      ModuleCat.restrictScalars.{u + 1}
        (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+* A).toRingHom ⋙
      Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)
    ∃ e : F.obj R ≅ G.obj R,
      ∀ a : A,
        F.map (ModuleCat.ofHom ((ULift.moduleEquiv (R := A) (M := A)).symm.toLinearMap.comp
          ((LinearMap.mulLeft A a).comp
            (ULift.moduleEquiv (R := A) (M := A)).toLinearMap))) ≫ e.hom =
          e.hom ≫ G.map (ModuleCat.ofHom
            ((ULift.moduleEquiv (R := A) (M := A)).symm.toLinearMap.comp
              ((LinearMap.mulLeft A a).comp
                (ULift.moduleEquiv (R := A) (M := A)).toLinearMap))) := by
  let eF := sectionValueIso l E X
  let eG := constantValueIso l E X
  refine ⟨eF ≪≫ eG.symm, ?_⟩
  intro a
  let A : Type u := Padic.coefficientExtensionIntegers l E
  let F :=
    (letI := (Padic.coefficientExtensionAbsoluteValue l E).toNormedField
     continuousScalarFunctor A) ⋙
      (upperStarFromPoint X).mapMod (DerivedNakayama.integerRing l E) ⋙
      integralSectionFunctor l E X ⋙ SheafOfModules.restrictScalars.{u + 1}
        (Scheme.integralDetailedCoefficientComparison X l E).hom
  let G := ModuleCat.restrictScalars.{u + 1}
    (ULift.ringEquiv : Scheme.PbcIntegralRing l E ≃+* A).toRingHom ⋙
    Scheme.integralConstantModule X (Scheme.pbcIntegralDatum l E)
  have h : eF.inv ≫ F.map (scalarEndo A a) ≫ eF.hom =
      eG.inv ≫ G.map (scalarEndo A a) ≫ eG.hom := by
    apply (SheafOfModules.unitHomEquiv _).injective
    apply PresheafOfModules.sections_ext
    intro U
    exact (sectionValueIso_scalar l E X a U).trans
      ((coefficientScalarCompatibility l E X a U).trans
        (constantValueIso_scalar l E X a U).symm)
  change F.map (scalarEndo A a) ≫ (eF.hom ≫ eG.inv) =
    (eF.hom ≫ eG.inv) ≫ G.map (scalarEndo A a)
  have h' := congrArg (fun z ↦ eF.hom ≫ z ≫ eG.inv) h
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id,
    Category.comp_id] using h'

end AlgebraicGeometry.ProEtale.IntegralSectionScalars
