/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.Proper.ProperFiniteCoefficientExtension
public import WeilConjectures.AlgebraicGeometry.Stratum.StratumScalarExtension
public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.Etale.Derived.EtaleDerivedScalarTensor
public import WeilConjectures.AlgebraicGeometry.Pur.PurEtaleScalarMateProjection
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.AlgebraicGeometry.Sf.SfCompactSupportRestrictionOfScalars
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicCompactSupport
public import WeilConjectures.AlgebraicGeometry.Canonical.CanonicalCompactSupportSiteComparison
public import WeilConjectures.AlgebraicGeometry.Sf.SfIntrinsicRealizationTransport
public import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection

/-!
# Canonical transport of the finite compact-support scalar mate

Source: Stacks Tags 0GL6 and 09AL; the scalar-mate compatibility of the etale and
pro-etale comparisons, followed by the normalized intrinsic realization.
(blueprint: lem-finite-compact-support-scalar-transport).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale.FiniteCompactScalar

/-- The scalar/open comparison fixed by uniqueness of the left adjoint. -/
@[irreducible] def openScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] (φ : A →+* B)
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (openImmersionLowerShriek (ModuleCat.{u + 1} A) j).mapDerivedCategory ⋙
        scalarExtension φ Z ≅
      scalarExtension φ X ⋙
        (openImmersionLowerShriek (ModuleCat.{u + 1} B) j).mapDerivedCategory := by
  let ea := upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} A) j
  let eb := upperStarIsoOpenImmersionRestriction (ModuleCat.{u + 1} B) j
  let adjA := ((openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} A) j).ofNatIsoRight ea.symm).mapDerivedCategoryAdjunction
  let adjB := ((openImmersionLowerShriekAdjunction
    (ModuleCat.{u + 1} B) j).ofNatIsoRight eb.symm).mapDerivedCategoryAdjunction
  let adjX := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ)
  let adjZ := Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars Z.smallEtaleTopology φ)
  let e := Functor.mapDerivedCategorySquareIso (upperStarRestrictScalarsIsoSheaf φ j)
  exact (adjA.comp adjZ).leftAdjointUniq ((adjX.comp adjB).ofNatIsoRight e.symm)

/-- Proper scalar extension followed by the open scalar comparison. -/
@[irreducible] def compactScalarIso
    {A B : Type (u + 1)} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [IsNoetherian c.Z] [IsNoetherian Y] :
    rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
        scalarExtension φ Y ≅
      scalarExtension φ X ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} B) c := by
  have : ∀ L, IsIso ((scalarMate φ c.g).app L) :=
    (properFiniteCoefficientExtension φ c.g).1
  have : IsIso (scalarMate φ c.g) := NatIso.isIso_of_isIso_app _
  let e := asIso (scalarMate φ c.g)
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft
      (openImmersionLowerShriek (ModuleCat.{u + 1} A) c.i).mapDerivedCategory e ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (openScalarIso φ c.i) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.Etale.FiniteCompactScalar

namespace AlgebraicGeometry.Scheme.FiniteCompactScalar

/-- The actual sheaf map of constant coefficient rings. -/
abbrev scalarRingMap
    {A B : Type u} [CommRing A] [CommRing B]
    (φ : A →+* B) (T : Scheme.{u}) :
    proEtaleConstantRing T A ⟶ proEtaleConstantRing T B :=
  proEtaleConstantRingMap (T := T) φ

/-- The scalar comparison through intrinsic realization, fixed by its right square. -/
@[irreducible] def realizationScalarIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    (sfIntrinsicDerivedEquivalence T A).functor ⋙
        pbcDerivedExtend.{u} (scalarRingMap φ T) ≅
      @ProEtale.pbcFixedScalarExtension.{u} T.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
          (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙
        (sfIntrinsicDerivedEquivalence T B).functor := by
  let EA := sfIntrinsicDerivedEquivalence T A
  let EB := sfIntrinsicDerivedEquivalence T B
  let ρ : proEtaleConstantRing T A ⟶ proEtaleConstantRing T B := scalarRingMap φ T
  let adj : pbcDerivedExtend.{u} ρ ⊣ pbcDerivedRestrict.{u} ρ := pbcDerivedScalarAdjunction ρ
  let rightIso : pbcDerivedRestrict.{u} ρ ⋙
      (sfIntrinsicModuleEquivalence T A).inverse.mapDerivedCategory ≅
      (sfIntrinsicModuleEquivalence T B).inverse.mapDerivedCategory ⋙
      @Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
        (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
        (RingHom.ulift.{u + 1, u + 1, u, u} φ) := by
    simpa only [ρ, pbcDerivedRestrict, pbcRestrict, scalarRingMap, proEtaleConstantRingMap,
      proEtaleCoefficientRestrictScalars, sfFixedRestriction, Sheaf.restrictScalars,
      Sheaf.derivedRestrictScalars] using
      Functor.mapDerivedCategorySquareIso (sfInverseRealizationRestriction T φ)
  let s : EA.functor ⋙ pbcDerivedExtend.{u} ρ ≅
      @ProEtale.pbcFixedScalarExtension.{u} T.ProEt inferInstance
          (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
          (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) ⋙ EB.functor :=
    ((EA.toAdjunction.comp adj).ofNatIsoRight
      rightIso).leftAdjointUniq
      ((Adjunction.ofIsRightAdjoint
        (@Sheaf.derivedRestrictScalars.{u} T.ProEt inferInstance
        (essentiallySmallSelf.{0, u, u + 1} _) (ProEt.topology T)
        (ULift.{u + 1, u} A) (ULift.{u + 1, u} B) inferInstance inferInstance
        (RingHom.ulift.{u + 1, u + 1, u, u} φ))).comp EB.toAdjunction)
  exact s

/-- The termwise factorization of intrinsic site comparison through realization. -/
def intrinsicSiteFunctorIso (A : Type u) [CommRing A] [Finite A] (T : Scheme.{u}) :
    ProEtale.finiteCoefficientIntrinsicDerivedComparison T A ≅
      (ProEtale.comparisonUpperStar
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) T).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence T A).functor :=
  (Functor.mapDerivedCategoryCompIso _ _).symm

/-- Site comparison and coefficient extension, in the intrinsic ringed presentation. -/
@[irreducible] def siteScalarIso
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) (T : Scheme.{u}) :
    ProEtale.finiteCoefficientIntrinsicDerivedComparison T A ⋙
        pbcDerivedExtend.{u} (scalarRingMap φ T) ≅
      Etale.scalarExtension.{u} (RingHom.ulift.{u + 1, u + 1, u, u} φ) T ⋙
        ProEtale.finiteCoefficientIntrinsicDerivedComparison T B :=
  Functor.isoWhiskerRight (intrinsicSiteFunctorIso A T) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (realizationScalarIso φ T) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (ProEtale.pbcComparisonReduction.{u} T (RingHom.ulift.{u + 1, u + 1, u, u} φ)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (intrinsicSiteFunctorIso B T).symm

/-- Compact support through realization, using the normalized proper comparison. -/
@[irreducible] def compactRealizationIso
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f) :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙ sfIntrinsicCompactSupport c A ≅
      ProEtale.rightDerivedLowerShriekOfCompactification
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c ⋙
        (sfIntrinsicDerivedEquivalence Y A).functor := by
  let EX := sfIntrinsicModuleEquivalence X A
  let EZ := sfIntrinsicModuleEquivalence c.Z A
  let J := ProEtale.openImmersionLowerShriek
    (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c.i
  let o : EX.functor ⋙ sfIntrinsicExtensionByZero c.i A ≅ J ⋙ EZ.functor :=
    EX.funInvIdAssoc (J ⋙ EZ.functor)
  let od := Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso o ≪≫ (Functor.mapDerivedCategoryCompIso _ _).symm
  exact (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight od _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (sfIntrinsicDerivedDirectImageComparison c.g A) ≪≫
    (Functor.associator _ _ _).symm

/-- The compact-support site comparison at a bounded-below etale input. -/
@[irreducible] def compactSiteIso
    (A : Type u) [CommRing A] [Finite A] {X Y : Scheme.{u}} {f : X ⟶ Y}
    (c : Compactification f)
    (G : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y A).obj
        ((Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) c).obj G.obj) ≅
      (sfIntrinsicCompactSupport c A).obj
        ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj) :=
  (intrinsicSiteFunctorIso A Y).app _ ≪≫
    (sfIntrinsicDerivedEquivalence Y A).functor.mapIso
      ((ProEtale.compactSupportSiteComparison (ULift.{u + 1, u} A) c).app G).symm ≪≫
    (compactRealizationIso A c).symm.app _ ≪≫
    (sfIntrinsicCompactSupport c A).mapIso ((intrinsicSiteFunctorIso A X).app G.obj).symm

/-- The explicit transported proper/open coefficient isomorphism at an etale origin. -/
@[irreducible] def intrinsicCompactScalarIsoOfOrigin
    {A B : Type u} [CommRing A] [CommRing B] [Finite A] [Finite B]
    (φ : A →+* B) {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f)
    [IsNoetherian c.Z] [IsNoetherian Y]
    (G : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A))))
    (GB : DerivedCategory.Plus
      (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} B))))
    (eGB : (Etale.scalarExtension (RingHom.ulift.{u + 1, u + 1, u, u} φ) X).obj G.obj ≅
      GB.obj) :
    (pbcDerivedExtend.{u} (scalarRingMap φ Y)).obj
        ((sfIntrinsicCompactSupport c A).obj
          ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj)) ≅
      (sfIntrinsicCompactSupport c B).obj
        ((pbcDerivedExtend.{u} (scalarRingMap φ X)).obj
          ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X A).obj G.obj)) :=
  (pbcDerivedExtend.{u} (scalarRingMap φ Y)).mapIso (compactSiteIso A c G).symm ≪≫
    (siteScalarIso φ Y).app _ ≪≫
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y B).mapIso
      ((Etale.FiniteCompactScalar.compactScalarIso
          (RingHom.ulift.{u + 1, u + 1, u, u} φ) c).app G.obj ≪≫
        (Etale.rightDerivedLowerShriekOfCompactification
          (ModuleCat.{u + 1} (ULift.{u + 1, u} B)) c).mapIso eGB) ≪≫
    compactSiteIso B c GB ≪≫
    (sfIntrinsicCompactSupport c B).mapIso
      ((ProEtale.finiteCoefficientIntrinsicDerivedComparison X B).mapIso eGB.symm ≪≫
        (siteScalarIso φ X).symm.app G.obj)

end AlgebraicGeometry.Scheme.FiniteCompactScalar
