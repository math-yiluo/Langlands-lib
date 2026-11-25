/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteCompactScalar.FiniteCompactSupportScalarTransportData

/-!
# The open and proper factors of the intrinsic site comparison

Source: Stacks Tags 09AF, 099R and 00YV. These are the two factors of the
canonical compact-support comparison, with its existing normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Scheme.FiniteCompactScalar

/-- Termwise realization of extension by zero, using the equivalence unit. -/
def openRealizationIso (A : Type u) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (sfIntrinsicDerivedEquivalence X A).functor ⋙
        (sfIntrinsicExtensionByZero j A).mapDerivedCategory ≅
      (ProEtale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        (sfIntrinsicDerivedEquivalence Z A).functor :=
  Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      ((sfIntrinsicModuleEquivalence X A).funInvIdAssoc
        (ProEtale.openImmersionLowerShriek
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j ⋙
          (sfIntrinsicModuleEquivalence Z A).functor)) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm

/-- The open site comparison followed by the normalized intrinsic realization. -/
def openSiteIso (A : Type u) [CommRing A] [Finite A]
    {X Z : Scheme.{u}} (j : X ⟶ Z) [IsOpenImmersion j] :
    (Etale.openImmersionLowerShriek
        (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j).mapDerivedCategory ⋙
        ProEtale.finiteCoefficientIntrinsicDerivedComparison Z A ≅
      ProEtale.finiteCoefficientIntrinsicDerivedComparison X A ⋙
        (sfIntrinsicExtensionByZero j A).mapDerivedCategory :=
  Functor.isoWhiskerLeft _ (intrinsicSiteFunctorIso A Z) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapDerivedCategorySquareIso
        (ProEtale.openImmersionLowerShriekComparisonUpperStarIso
          (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) j)) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (openRealizationIso A j).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (intrinsicSiteFunctorIso A X).symm _

/-- The proper direct-image site mate in ambient derived categories, using D+ only
at the input. All inclusion comparisons are the published canonical comparisons. -/
def properSiteIso (A : Type u) [CommRing A] [Finite A]
    {Z Y : Scheme.{u}} (g : Z ⟶ Y) [QuasiCompact g] [QuasiSeparated g]
    (H : DerivedCategory.Plus
      (Sheaf Z.smallEtaleTopology (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))) :
    (ProEtale.finiteCoefficientIntrinsicDerivedComparison Y A).obj
        ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g).rightDerivedFunctor.obj
          H.obj) ≅
      (proEtaleConstantDerivedDirectImage g A).obj
        ((ProEtale.finiteCoefficientIntrinsicDerivedComparison Z A).obj H.obj) := by
  let N := ProEtale.comparisonUpperStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A))
  let re := Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g
  let rp := ProEtale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1, u} A)) g
  letI := ProEtale.isIso_fixedComparisonDirectImageMatePlus (ULift.{u + 1, u} A) g
  exact (intrinsicSiteFunctorIso A Y).app _ ≪≫
    (sfIntrinsicDerivedEquivalence Y A).functor.mapIso
      ((N Y).mapDerivedCategory.mapIso (re.rightDerivedFunctorPlusCompatibility.app H).symm ≪≫
        ((N Y).mapDerivedCategoryPlusCompatibility.app
          (re.rightDerivedFunctorPlus.obj H)).symm ≪≫
        DerivedCategory.Plus.ι.mapIso
          ((asIso (ProEtale.fixedComparisonDirectImageMatePlus
            (ULift.{u + 1, u} A) g)).app H) ≪≫
        (rp.rightDerivedFunctorPlusCompatibility.app ((N Z).mapDerivedCategoryPlus.obj H)) ≪≫
        rp.rightDerivedFunctor.mapIso ((N Z).mapDerivedCategoryPlusCompatibility.app H)) ≪≫
    (sfIntrinsicDerivedDirectImageComparison g A).symm.app ((N Z).mapDerivedCategory.obj H.obj) ≪≫
    (proEtaleConstantDerivedDirectImage g A).mapIso
      ((intrinsicSiteFunctorIso A Z).app H.obj).symm

end AlgebraicGeometry.Scheme.FiniteCompactScalar
