/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Proper.ProEtaleProperOpenComparison
public import WeilConjectures.AlgebraicGeometry.FixedComparisonDirectImageMate
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.LowerShriekComparison

/-! # Canonical compactification site comparison

Source: Stacks Project, Tags 09AF and 099R; blueprint order 1806
(blueprint: proposition-comparison-immersions--4).
The proper factor is the specified counit mate, rather than a choice of an isomorphism.
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory
namespace AlgebraicGeometry.ProEtale

/-- The compact-support site comparison on bounded below complexes, from the exact open
comparison and the canonical proper direct-image mate. Source: Stacks Tags 09AF and 099R
(blueprint: proposition-comparison-immersions--4). -/
def compactSupportSiteComparisonPlus (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    Etale.rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlus ≅
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlus ⋙
        rightDerivedLowerShriekOfCompactificationPlus (ModuleCat.{u + 1} A) c :=
  letI := isIso_fixedComparisonDirectImageMatePlus A c.g
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (asIso (fixedComparisonDirectImageMatePlus A c.g)) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (properOpenSiteExtensionIso A c.i) _ ≪≫
    Functor.associator _ _ _

/-- The same comparison in the ambient categories, oriented from pro-etale compact
support to comparison pullback of etale compact support. A witness is inserted by
naturality, so the construction applies to every isomorphic pro-etale realization.
Source: Stacks Tags 09AF and 099R
(blueprint: proposition-comparison-immersions--4). -/
def compactSupportSiteComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    DerivedCategory.Plus.ι ⋙ (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory ⋙
        rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ≅
      DerivedCategory.Plus.ι ⋙
        Etale.rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c ⋙
          (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategoryPlusCompatibility.symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (compactSupportSiteComparisonPlus A c).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategoryPlusCompatibility ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.rightDerivedLowerShriekOfCompactificationPlusCompatibility
        (ModuleCat.{u + 1} A) c) _ ≪≫
    Functor.associator _ _ _

end AlgebraicGeometry.ProEtale
