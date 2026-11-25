/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.Etale.Origin.EtaleOriginScalarPullbackData
import all WeilConjectures.AlgebraicGeometry.Etale.ProEtale.EtaleProEtaleScalarPullbackCube
import all WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteRealizationRestrictionCube
import all WeilConjectures.AlgebraicGeometry.ProEtale.Fixed.ProEtaleFixedScalarRestrictionDirectImage
import all WeilConjectures.AlgebraicGeometry.ProEtale.Ring.ProEtaleRingSheafChangeAdjunctionSupplement
import WeilConjectures.SmoothPurity.Compact.CompactSupportScalarDirectNormalization

/-! # Intrinsic realization and scalar pullback coherence -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option maxRecDepth 2000
set_option backward.defeqAttrib.useBackward true
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale
attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor
  Etale.scalarTensorIso Scheme.completedAdicDerivedChange
attribute [local implicit_reducible] Equivalence.mapDerivedCategory
  Scheme.sfIntrinsicDerivedEquivalence

private theorem mate_whisker_top
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {G G' : C ⥤ E} {H : D ⥤ F}
    {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (w : TwoSquare G' L₁ L₂ H) (t : G ⟶ G') :
    mateEquiv a₁ a₂ (w.whiskerTop t) = (mateEquiv a₁ a₂ w).whiskerRight t := by
  simpa [TwoSquare.whiskerBottom, TwoSquare.whiskerLeft] using
    mateEquiv_whiskerTop_whiskerBottom a₁ a₂ w t (𝟙 H)

private theorem inverse_mate_cube
    {CA DA CB DB EA FA EB FB : Type*}
    [Category CA] [Category DA] [Category CB] [Category DB]
    [Category EA] [Category FA] [Category EB] [Category FB]
    {LA : CA ⥤ DA} {RA : DA ⥤ CA} {LB : CB ⥤ DB} {RB : DB ⥤ CB}
    {LA' : EA ⥤ FA} {RA' : FA ⥤ EA} {LB' : EB ⥤ FB} {RB' : FB ⥤ EB}
    (aA : LA ⊣ RA) (aB : LB ⊣ RB) (bA : LA' ⊣ RA') (bB : LB' ⊣ RB')
    {U : CB ⥤ CA} {V : DB ⥤ DA} {U' : EB ⥤ EA} {V' : FB ⥤ FA}
    {GA : CA ⥤ EA} {HA : DA ⥤ FA} {GB : CB ⥤ EB} {HB : DB ⥤ FB}
    (aa : TwoSquare GA LA LA' HA) (ab : TwoSquare GB LB LB' HB)
    (k : TwoSquare U LB LA V) (i : TwoSquare U' LB' LA' V')
    (t : U ⋙ GA ⟶ GB ⋙ U') (s : V ⋙ HA ⟶ HB ⋙ V')
    (h : ∀ M : DB,
      t.app (RB.obj M) ≫ U'.map ((mateEquiv aB bB ab).app M) ≫
          (mateEquiv bB bA i).app (HB.obj M) =
        GA.map ((mateEquiv aB aA k).app M) ≫
          (mateEquiv aA bA aa).app (V.obj M) ≫ RA'.map (s.app M))
    (N : CB) :
    LA'.map (t.app N) ≫ i.app (GB.obj N) ≫ V'.map (ab.app N) =
      aa.app (U.obj N) ≫ HA.map (k.app N) ≫ s.app (LB.obj N) := by
  have hc : (ab.hComp i).whiskerTop t = (k.hComp aa).whiskerBottom s := by
    apply (mateEquiv aB bA).injective
    rw [mate_whisker_top, mateEquiv_whiskerBottom,
      mateEquiv_vcomp aB bB bA, mateEquiv_vcomp aB aA bA]
    ext M
    simpa only [TwoSquare.vComp, TwoSquare.whiskerRight, TwoSquare.whiskerLeft,
      NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.associator_inv_app,
      Category.id_comp, Category.comp_id, Category.assoc] using h M
  simpa only [TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using
    congrArg (fun w ↦ w.app N) hc

private theorem right_derived_unit_naturality
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (τ : F ⟶ G) (I : CochainComplex C ℤ) :
    F.rightDerivedFunctorUnitQ I ≫
        (Functor.rightDerivedFunctorNatTrans τ).app (DerivedCategory.Q.obj I) =
      DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app I) ≫
        G.rightDerivedFunctorUnitQ I := by
  have h₁ := (Functor.rightDerivedFunctorNatTrans τ).naturality
    ((DerivedCategory.quotientCompQhIso C).hom.app I)
  have h₂ := Functor.rightDerivedNatTrans_app F.rightDerivedFunctor G.rightDerivedFunctor
    F.rightDerivedFunctorUnit G.rightDerivedFunctorUnit
    (HomotopyCategory.quasiIso C (.up ℤ))
    (Functor.whiskerRight (NatTrans.mapHomotopyCategory τ (.up ℤ)) DerivedCategory.Qh)
    ((HomotopyCategory.quotient _ _).obj I)
  have h₃ := (DerivedCategory.quotientCompQhIso D).inv.naturality
    ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app I)
  dsimp only [Functor.comp_map] at h₁ h₃
  simp only [Functor.rightDerivedFunctorUnitQ, Category.assoc]
  erw [h₁, reassoc_of% h₂, ← reassoc_of% h₃]

private theorem normalized_horizontal_naturality
    {A B C D : Type*}
    [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    [Abelian.HasKInjectiveResolutions A] [Abelian.HasKInjectiveResolutions C]
    (F F' : A ⥤ B) (G G' : C ⥤ D) (x : A ⥤ C) (y : B ⥤ D)
    [F.Additive] [F'.Additive] [G.Additive] [G'.Additive] [x.Additive] [y.Additive]
    [PreservesFiniteLimits x] [PreservesFiniteColimits x]
    [PreservesFiniteLimits y] [PreservesFiniteColimits y]
    (c : F ⋙ y ⟶ x ⋙ G) (c' : F' ⋙ y ⟶ x ⋙ G')
    (b : F.rightDerivedFunctor ⋙ y.mapDerivedCategory ⟶
      x.mapDerivedCategory ⋙ G.rightDerivedFunctor)
    (b' : F'.rightDerivedFunctor ⋙ y.mapDerivedCategory ⟶
      x.mapDerivedCategory ⋙ G'.rightDerivedFunctor)
    (hb : MixedDerivedCube.unitNormalized F G x y x.mapDerivedCategory y.mapDerivedCategory
      x.mapDerivedCategoryFactors y.mapDerivedCategoryFactors c b)
    (hb' : MixedDerivedCube.unitNormalized F' G' x y x.mapDerivedCategory y.mapDerivedCategory
      x.mapDerivedCategoryFactors y.mapDerivedCategoryFactors c' b')
    (e : F ⟶ F') (f : G ⟶ G')
    (hc : ∀ M, y.map (e.app M) ≫ c'.app M = c.app M ≫ f.app (x.obj M)) :
    Functor.whiskerRight (Functor.rightDerivedFunctorNatTrans e) y.mapDerivedCategory ≫ b' =
      b ≫ Functor.whiskerLeft x.mapDerivedCategory (Functor.rightDerivedFunctorNatTrans f) := by
  apply MixedDerivedCube.derived_unit_ext_general F y.mapDerivedCategory
  intro I
  apply (cancel_mono
    (G'.rightDerivedFunctor.map (x.mapDerivedCategoryFactors.hom.app I))).mp
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc]
  rw [← y.mapDerivedCategory.map_comp_assoc, right_derived_unit_naturality,
    y.mapDerivedCategory.map_comp, Category.assoc, hb' I]
  rw [reassoc_of% (y.mapDerivedCategoryFactors.hom.naturality
    ((NatTrans.mapHomologicalComplex e (.up ℤ)).app I))]
  rw [← DerivedCategory.Q.map_comp_assoc]
  have hcI : (y.mapHomologicalComplex (.up ℤ)).map
        ((NatTrans.mapHomologicalComplex e (.up ℤ)).app I) ≫
      (NatTrans.mapHomologicalComplex c' (.up ℤ)).app I =
    (NatTrans.mapHomologicalComplex c (.up ℤ)).app I ≫
      (NatTrans.mapHomologicalComplex f (.up ℤ)).app
        ((x.mapHomologicalComplex (.up ℤ)).obj I) := by
    ext n
    exact hc (I.X n)
  rw [hcI, DerivedCategory.Q.map_comp, Category.assoc, ← right_derived_unit_naturality]
  rw [← reassoc_of% (hb I)]
  rw [← (Functor.rightDerivedFunctorNatTrans f).naturality]
  rfl

private theorem site_pullback_normalization
    (A : Type (u + 1)) [CommRing A] {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    (comparisonOpenDerivedPullbackIso A p).inv =
      (directImageComparisonAmbientPullbackIso A p).hom := by
  have hn : Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) p).symm =
      (Functor.mapDerivedCategoryNatIso
        (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) p)).symm :=
    Iso.ext (Functor.mapDerivedCategoryNatIso_symm _)
  simp only [comparisonOpenDerivedPullbackIso, directImageComparisonAmbientPullbackIso,
    supportComparison_eq, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerRight_inv,
    hn, Category.assoc]

private def origin_ordinary_push_iso (A : Type u) [CommRing A]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) :
    Scheme.proEtaleRingModuleDirectImage p
        (Scheme.proEtaleConstantRing Y A) (Scheme.proEtaleConstantRing Z A)
        (Scheme.proEtaleConstantRingComparison p A) ≅
      Scheme.proEtaleConstantModuleDirectImage p A :=
  SheafOfModules.pushforwardCongr
    (congrArg (fun g : Scheme.proEtaleConstantRing Y A ⟶
        (Scheme.proEtaleSheafDirectImage p CommRingCat.{u + 1}).obj
          (Scheme.proEtaleConstantRing Z A) ↦
      (sheafCompose (Scheme.ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).map g)
      ((Scheme.proEtaleSheafAdjunction p CommRingCat.{u + 1}).homEquiv _ _
        |>.apply_symm_apply (Scheme.proEtaleCoefficientDirectImageMap p A)))

private theorem origin_restriction_push_normalization
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (M : Scheme.proEtaleDerivedCategory Z B) :
    (scalarMateRestriction φ Y).mapDerivedCategory.map
        ((properOriginPushIso B p).hom.app M) ≫
      (Scheme.sfDerivedImageRestriction p φ).inv.app M =
    (mateEquiv (directImageConstantAdjunction B p) (directImageConstantAdjunction A p)
      (TwoSquare.mk _ _ _ _ (originRestrictionPullback φ p))).app M ≫
      (properOriginPushIso A p).hom.app
        ((scalarMateRestriction φ Z).mapDerivedCategory.obj M) := by
  let F (R : Type u) [CommRing R] := Scheme.proEtaleRingModuleDirectImage p
    (Scheme.proEtaleConstantRing Y R) (Scheme.proEtaleConstantRing Z R)
    (Scheme.proEtaleConstantRingComparison p R)
  let x := scalarMateRestriction φ Z
  let y := scalarMateRestriction φ Y
  let c := Scheme.proEtaleRingRestrictionDirectImage p
    (Scheme.proEtaleConstantRing Y A) (Scheme.proEtaleConstantRing Y B)
    (Scheme.proEtaleConstantRing Z A) (Scheme.proEtaleConstantRing Z B)
    (Scheme.proEtaleConstantRingMap (T := Y) φ)
    (Scheme.proEtaleConstantRingMap (T := Z) φ)
    (Scheme.proEtaleConstantRingComparison p A) (Scheme.proEtaleConstantRingComparison p B)
    (Scheme.proEtaleConstantInverseImageMap_naturality p
      (CommRingCat.ofHom (RingHom.ulift φ))).symm
  let b := (mateEquiv (directImageConstantAdjunction B p)
    (directImageConstantAdjunction A p)
    (TwoSquare.mk _ _ _ _ (originRestrictionPullback φ p)))
  have hb : MixedDerivedCube.unitNormalized (F B) (F A) x y
      x.mapDerivedCategory y.mapDerivedCategory x.mapDerivedCategoryFactors
      y.mapDerivedCategoryFactors c.hom b := by
    intro I
    simpa only [F, x, y, b, c, Scheme.canonicalDerivedMate, chainDerivedUnit,
      Functor.rightDerivedFunctorUnitQ, originRestrictionPullback, directImageConstantAdjunction,
      NatIso.mapHomologicalComplex] using Scheme.canonicalDerivedMate_factors p
      (Scheme.proEtaleConstantRing Y A) (Scheme.proEtaleConstantRing Y B)
      (Scheme.proEtaleConstantRing Z A) (Scheme.proEtaleConstantRing Z B)
      (Scheme.proEtaleConstantRingMap (T := Y) φ)
      (Scheme.proEtaleConstantRingMap (T := Z) φ)
      (Scheme.proEtaleConstantRingComparison p A) (Scheme.proEtaleConstantRingComparison p B)
      (Scheme.proEtaleConstantInverseImageMap_naturality p
        (CommRingCat.ofHom (RingHom.ulift φ))).symm I
  have hb' := WeilConjectures.compactSupportScalarDirectNormalization p φ
  have hc (L : Scheme.proEtaleRingModules Z (Scheme.proEtaleConstantRing Z B)) :
      y.map ((origin_ordinary_push_iso B p).hom.app L) ≫
        (Scheme.proEtaleCoefficientDirectImageComparison p φ).hom.app L =
      c.hom.app L ≫ (origin_ordinary_push_iso A p).hom.app (x.obj L) := by
    apply SheafOfModules.hom_ext
    apply PresheafOfModules.hom_ext
    intro W
    ext n
    change ((Scheme.proEtaleCoefficientDirectImageComparison p φ).hom.app L).val.app W n =
      (c.hom.app L).val.app W n
    have hc' := (Scheme.proEtaleCoefficientDirectImageComparison_existsUnique p φ).choose_spec.1
      L W n
    have hc'' := (Scheme.proEtaleRingRestrictionDirectImage_existsUnique p
      (Scheme.proEtaleConstantRing Y A) (Scheme.proEtaleConstantRing Y B)
      (Scheme.proEtaleConstantRing Z A) (Scheme.proEtaleConstantRing Z B)
      (Scheme.proEtaleConstantRingMap (T := Y) φ)
      (Scheme.proEtaleConstantRingMap (T := Z) φ)
      (Scheme.proEtaleConstantRingComparison p A) (Scheme.proEtaleConstantRingComparison p B)
      (Scheme.proEtaleConstantInverseImageMap_naturality p
        (CommRingCat.ofHom (RingHom.ulift φ))).symm).choose_spec.1 L W n
    exact hc'.trans hc''.symm
  have h := normalized_horizontal_naturality (F B)
    (Scheme.proEtaleConstantModuleDirectImage p B) (F A)
    (Scheme.proEtaleConstantModuleDirectImage p A) x y c.hom
    (Scheme.proEtaleCoefficientDirectImageComparison p φ).hom b
    (Scheme.sfDerivedImageRestriction p φ).inv hb hb'
    (origin_ordinary_push_iso B p).hom (origin_ordinary_push_iso A p).hom hc
  simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    properOriginPushIso, Functor.rightDerivedFunctorNatIso, origin_ordinary_push_iso,
    b, x, y] using NatTrans.congr_app h M

private def realization_restriction_iso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :=
  Functor.mapDerivedCategorySquareIso (Scheme.sfRealizationRestriction T φ)

private def realization_pullback (A : Type u) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (p : Z ⟶ Y) :=
  ((mateEquiv
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p)
    (directImageConstantAdjunction A p)).symm
      (TwoSquare.mk _ _ _ _ (originRealizationPushIso A p).inv))

private theorem realization_restriction_right_cube
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (M : DerivedCategory
      (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))) :
    let r (T : Scheme.{u}) := realization_restriction_iso φ T
    (r Y).inv.app
        ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) p).rightDerivedFunctor.obj M) ≫
      (scalarMateRestriction φ Y).mapDerivedCategory.map
        ((originRealizationPushIso B p).inv.app M) ≫
      (mateEquiv (directImageConstantAdjunction B p) (directImageConstantAdjunction A p)
        (TwoSquare.mk _ _ _ _ (originRestrictionPullback φ p))).app
        ((Scheme.sfIntrinsicDerivedEquivalence Z B).functor.obj M) =
    (Scheme.sfIntrinsicDerivedEquivalence Y A).functor.map
        ((fixedScalarRestrictionDirectImage (RingHom.ulift.{u + 1, u + 1, u, u} φ) p).inv.app M) ≫
      (originRealizationPushIso A p).inv.app
        ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z)
          (RingHom.ulift.{u + 1, u + 1, u, u} φ)).obj M) ≫
      (directImageConstantPush A p).map ((r Z).inv.app M) := by
  dsimp only
  let r (T : Scheme.{u}) := realization_restriction_iso φ T
  have h := Scheme.FiniteCompactScalar.realizationRestriction_directImage_cube φ p M
  rw [Scheme.FiniteCompactScalar.restriction_eq,
    Scheme.FiniteCompactScalar.restriction_eq] at h
  have he :
      ((Scheme.proEtaleConstantDerivedDirectImage p A).mapIso ((r Z).app M) ≪≫
        (Scheme.sfIntrinsicDerivedDirectImageComparison p A).app
          ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Z)
            (RingHom.ulift.{u + 1, u + 1, u, u} φ)).obj M) ≪≫
        (Scheme.sfIntrinsicDerivedEquivalence Y A).functor.mapIso
          ((fixedScalarRestrictionDirectImage
            (RingHom.ulift.{u + 1, u + 1, u, u} φ) p).app M)) =
      ((Scheme.sfDerivedImageRestriction p φ).app
          ((Scheme.sfIntrinsicDerivedEquivalence Z B).functor.obj M) ≪≫
        (scalarMateRestriction φ Y).mapDerivedCategory.mapIso
          ((Scheme.sfIntrinsicDerivedDirectImageComparison p B).app M) ≪≫
        (r Y).app
          ((lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) p).rightDerivedFunctor.obj M)) :=
    Iso.ext h
  have hi := congrArg Iso.inv he
  simp only [Iso.trans_inv, Functor.mapIso_inv, Iso.app_inv, Category.assoc] at hi
  have hn := origin_restriction_push_normalization φ p
    ((Scheme.sfIntrinsicDerivedEquivalence Z B).functor.obj M)
  have hn' := congrArg (fun f ↦
    (scalarMateRestriction φ Y).mapDerivedCategory.map
        ((properOriginPushIso B p).inv.app
          ((Scheme.sfIntrinsicDerivedEquivalence Z B).functor.obj M)) ≫ f ≫
      (properOriginPushIso A p).inv.app
        ((scalarMateRestriction φ Z).mapDerivedCategory.obj
          ((Scheme.sfIntrinsicDerivedEquivalence Z B).functor.obj M))) hn
  simp only [Category.assoc, ← Functor.map_comp_assoc, Iso.inv_hom_id_app,
    Iso.hom_inv_id_app] at hn'
  erw [(scalarMateRestriction φ Y).mapDerivedCategory.map_id,
    Category.id_comp, Category.comp_id] at hn'
  have hpush (R : Type u) [CommRing R] [Finite R]
      (K : DerivedCategory
        (Sheaf (Scheme.ProEt.topology Z) (ModuleCat.{u + 1} (ULift.{u + 1, u} R)))) :
      (originRealizationPushIso R p).inv.app K =
        (Scheme.sfIntrinsicDerivedDirectImageComparison p R).inv.app K ≫
          (properOriginPushIso R p).inv.app
            ((Scheme.sfIntrinsicDerivedEquivalence Z R).functor.obj K) := rfl
  rw [hpush, hpush, Functor.map_comp]
  simp only [Category.assoc]
  rw [← hn']
  rw [← reassoc_of% hi]
  erw [(properOriginPushIso A p).inv.naturality]
  rfl

private theorem realization_restriction_pullback_cube
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (M : DerivedCategory
      (Sheaf (Scheme.ProEt.topology Y) (ModuleCat.{u + 1} (ULift.{u + 1, u} B)))) :
    let r (T : Scheme.{u}) := realization_restriction_iso φ T
    (Scheme.proEtaleConstantRingDerivedPullback A p).map ((r Y).inv.app M) ≫
      (originRestrictionPullback φ p).app
        ((Scheme.sfIntrinsicDerivedEquivalence Y B).functor.obj M) ≫
      (scalarMateRestriction φ Z).mapDerivedCategory.map ((realization_pullback B p).app M) =
    (realization_pullback A p).app
        ((Sheaf.derivedRestrictScalars (Scheme.ProEt.topology Y)
          (RingHom.ulift.{u + 1, u + 1, u, u} φ)).obj M) ≫
      (Scheme.sfIntrinsicDerivedEquivalence Z A).functor.map
        ((leftDerivedUpperStarRestrictScalarsIso
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) p).hom.app M) ≫
      (r Z).inv.app
        ((upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) p).leftDerivedFunctor.obj M) := by
  apply inverse_mate_cube
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) p)
    (directImageConstantAdjunction A p) (directImageConstantAdjunction B p)
    (TwoSquare.mk _ _ _ _ (realization_pullback A p))
    (TwoSquare.mk _ _ _ _ (realization_pullback B p))
    (TwoSquare.mk _ _ _ _ (leftDerivedUpperStarRestrictScalarsIso
      (RingHom.ulift.{u + 1, u + 1, u, u} φ) p).hom)
    (TwoSquare.mk _ _ _ _ (originRestrictionPullback φ p))
    (realization_restriction_iso φ Y).inv
    (realization_restriction_iso φ Z).inv ?_ M
  intro L
  simpa only [realization_pullback, realization_restriction_iso, Equiv.apply_symm_apply,
    fixedScalarRestrictionDirectImage, fixedScalarRestrictionDirectImageMap,
    fixedScalarRestrictionPullback, Iso.symm_inv, asIso_hom] using
    realization_restriction_right_cube φ p L

private theorem origin_pullback_decomposition
    (A : Type u) [CommRing A] [Finite A] {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (N : Etale.DerivedCategoryModule (ULift.{u + 1, u} A) Y) :
    (originPullback A p).app N =
      (Scheme.proEtaleConstantRingDerivedPullback A p).map
          ((Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A Y).hom.app N) ≫
        (realization_pullback A p).app
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) Y).mapDerivedCategory.obj
            N) ≫
        (Scheme.sfIntrinsicDerivedEquivalence Z A).functor.map
          ((comparisonOpenDerivedPullbackIso (ULift.{u + 1, u} A) p).inv.app N) ≫
        (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A Z).inv.app
          ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p).leftDerivedFunctor.obj
            N) := by
  let ae := Etale.derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p
  let ap := derivedUpperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) p
  let ai := directImageConstantAdjunction A p
  let s := TwoSquare.mk _ _ _ _ (comparisonOpenDerivedPullbackIso
    (ULift.{u + 1, u} A) p).inv
  let r := TwoSquare.mk _ _ _ _ (realization_pullback A p)
  have hc : TwoSquare.mk _ _ _ _ (originPullback A p) =
      ((s.hComp r).whiskerTop
        (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A Y).hom).whiskerBottom
          (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A Z).inv := by
    apply (mateEquiv ae ai).injective
    rw [mateEquiv_whiskerBottom, mate_whisker_top, mateEquiv_vcomp ae ap ai]
    simp only [originPullback, r, realization_pullback, ae, ap, ai,
      TwoSquare.mk,
      Equiv.apply_symm_apply]
    ext M
    simp only [originMate, TwoSquare.vComp, TwoSquare.whiskerLeft,
      TwoSquare.whiskerRight, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Category.id_comp, Category.assoc]
    rfl
  simpa only [s, r, TwoSquare.hComp, TwoSquare.whiskerTop, TwoSquare.whiskerBottom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] using
    congrArg (fun w ↦ w.app N) hc

private theorem origin_restriction_inv_app
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u})
    (N : Etale.DerivedCategoryModule (ULift.{u + 1, u} B) T) :
    (properOriginRestrictionIso φ T).inv.app N =
      (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A T).hom.app
          ((Sheaf.derivedRestrictScalars T.smallEtaleTopology
            (RingHom.ulift.{u + 1, u + 1, u, u} φ)).obj N) ≫
        (Scheme.sfIntrinsicDerivedEquivalence T A).functor.map
          ((pbcDerivedComparisonRestrict T (RingHom.ulift.{u + 1, u + 1, u, u} φ)).inv.app N) ≫
        (realization_restriction_iso φ T).inv.app
          ((comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) T).mapDerivedCategory.obj
            N) ≫
        (scalarMateRestriction φ T).mapDerivedCategory.map
          ((Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso B T).inv.app N) := by
  simp only [properOriginRestrictionIso, realization_restriction_iso,
    Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerLeft_inv, Functor.isoWhiskerRight_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.assoc]
  rfl

/-- The restriction/realization comparison commutes with geometric pullback.
Source: Stacks 03EL, 0D6D and 07A6; restriction part of the coefficient comparison
in Tag 0E48 (blueprint: lem-fix-etale-origin-restriction-pullback-cube).

Proof: compare the ordinary right-adjoint squares on sections: the coefficient
comparison, the restriction square, and the pushforwardCongr maps are all the
identity on sections. Their right-derived squares are characterized by the
all-complex derived-unit normalization. Naturality of that normalization identifies
the canonical restriction mate with sfDerivedImageRestriction.inv after conjugation
by properOriginPushIso; restriction need not preserve K-injectives.
Invert realizationRestriction_directImage_cube and insert this identification.
Compatibility of mates with pasting gives the intrinsic realization/pullback cube.
The same compatibility expands originPullback as the fixed-site comparison followed
by the intrinsic realization mate, transported by intrinsicSiteFunctorIso. Paste
this cube with derived_restriction_cube for the etale/pro-etale site comparison,
using supportComparison_eq to identify its specified site map. Naturality cancels
the intermediate realization isomorphisms and gives the inverse-endpoint formula.
This uses no tensor comparison or extension of scalars, and no bound on N.
The argument applies unchanged to zero rings, zero complexes and empty schemes. -/
theorem etaleOriginRestrictionPullbackCube
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {Z Y : Scheme.{u}} (p : Z ⟶ Y)
    (N : Etale.DerivedCategoryModule (ULift.{u + 1, u} B) Y) :
    (Scheme.proEtaleConstantRingDerivedPullback A p).map
        ((properOriginRestrictionIso φ Y).inv.app N) ≫
      (originRestrictionPullback φ p).app
        ((finiteCoefficientIntrinsicDerivedComparison Y B).obj N) ≫
      (scalarMateRestriction φ Z).mapDerivedCategory.map ((originPullback B p).app N) =
    (originPullback A p).app
        ((Sheaf.derivedRestrictScalars Y.smallEtaleTopology
          (RingHom.ulift.{u + 1, u + 1, u, u} φ)).obj N) ≫
      (finiteCoefficientIntrinsicDerivedComparison Z A).map
        ((Etale.scalarRestrictionPullbackIso
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) p).hom.app N) ≫
      (properOriginRestrictionIso φ Z).inv.app
        ((Etale.upperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) p).leftDerivedFunctor.obj
          N) := by
  let a := RingHom.ulift.{u + 1, u + 1, u, u} φ
  let CYB := (comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) Y).mapDerivedCategory
  let EZA := (Scheme.sfIntrinsicDerivedEquivalence Z A).functor
  let UY := (scalarMateRestriction φ Y).mapDerivedCategory
  let LA := Scheme.proEtaleConstantRingDerivedPullback A p
  have hs := derived_restriction_cube a p N
  rw [← site_pullback_normalization, ← site_pullback_normalization] at hs
  have hs' := congrArg EZA.map hs
  simp only [Functor.map_comp] at hs'
  have hr := realization_restriction_pullback_cube φ p (CYB.obj N)
  have hy := (originRestrictionPullback φ p).naturality
    ((Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso B Y).hom.app N)
  have hn := (realization_pullback A p).naturality
    ((pbcDerivedComparisonRestrict Y a).inv.app N)
  have hz := (realization_restriction_iso φ Z).inv.naturality
    ((comparisonOpenDerivedPullbackIso (ULift.{u + 1, u} B) p).inv.app N)
  have he := (Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso A Z).inv.naturality
    ((Etale.scalarRestrictionPullbackIso a p).hom.app N)
  dsimp only [Functor.comp_map] at hy hn hz he
  simp only [origin_restriction_inv_app, origin_pullback_decomposition,
    Functor.map_comp, Category.assoc]
  erw [← reassoc_of% he, Iso.inv_hom_id_app_assoc]
  erw [← reassoc_of% hy]
  erw [Iso.inv_hom_id_map_assoc
    ((Scheme.FiniteCompactScalar.intrinsicSiteFunctorIso B Y).app N) (UY ⋙ LA)]
  erw [reassoc_of% hr, reassoc_of% hn, ← reassoc_of% hz]
  erw [reassoc_of% hs']

end AlgebraicGeometry.ProEtale
