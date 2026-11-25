/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.Grp.LeftExactFunctor
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import WeilConjectures.Algebra.Homology.LiftToInjectiveUniqueUpToHomotopy
public import WeilConjectures.Algebra.Homology.LocalizedRestrictionAdjunction
public import WeilConjectures.AlgebraicGeometry.ComparisonPullbackCoherence
public import WeilConjectures.AlgebraicGeometry.DerivedEtaleCohomologyLimit
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageKanRepresentative
public import WeilConjectures.AlgebraicGeometry.EtaleSectionsFpqcDescent
public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonComposition
public import WeilConjectures.AlgebraicGeometry.EtaleSetSectionComparisonIdentity
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalRestriction
public import WeilConjectures.AlgebraicGeometry.EtaleSetTerminalTransport
public import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
public import WeilConjectures.AlgebraicGeometry.ProEtaleClassicalSheavesImage
public import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperationsCanonicalAdjunction
public import WeilConjectures.AlgebraicGeometry.ProEtaleQcqsFiniteFamilyGeometry
public import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
public import WeilConjectures.AlgebraicGeometry.SiteRestrictionInjectives
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.AcyclicComparisonNatural
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp
public import WeilConjectures.CategoryTheory.ConstantLeftModuleTransport
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.CategoryTheory.DerivedCategory.PlusDevissage
public import WeilConjectures.CategoryTheory.RightDerivedExactComposite
public import WeilConjectures.CategoryTheory.RightDerivedPlusCube
public import WeilConjectures.CategoryTheory.RingedDerivedRestrictionGeneral
public import WeilConjectures.CategoryTheory.RingedSiteModulesGrothendieckOfUniverses
public import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
public import WeilConjectures.CategoryTheory.SiteExtensionByZeroPresheaf
public import WeilConjectures.CategoryTheory.SitePullbackAbelianUnderlying
public import WeilConjectures.CategoryTheory.Sites.CohomologyRightDerivedSections
public import WeilConjectures.CategoryTheory.Sites.InjectiveModuleAbelianAcyclic
public import WeilConjectures.Mathlib.CategoryTheory.Adjunction.Restrict
public import WeilConjectures.Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence
public import WeilConjectures.SixFunctors.ProEtale.Comparison.CohomologicalDimension
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison

/-! # The canonical unbounded direct-image mate

The constructions are reexported by `UnboundedDirectImageComparison`.
Source: blueprint `sk-prop-pe-unbounded-classical-direct-image.md`.
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

/-- Apply the exact inverse images termwise and localize the specified comparison square.
Source: blueprint, sk-prop-pe-unbounded-classical-direct-image.md; the inverse-image
comparison is theorem-comparison-direct-images
(auxiliary; not a blueprint node). -/
noncomputable def unboundedDirectImagePullbackIso
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory ⋙
        (ProEtale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) g).mapDerivedCategory ⋙
        (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory :=
  Functor.mapDerivedCategoryCompIso
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y)
    (ProEtale.upperStar (ModuleCat.{u + 1} A) g) ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) g) ≪≫
    (Functor.mapDerivedCategoryCompIso
      (Etale.upperStar (ModuleCat.{u + 1} A) g)
      (comparisonUpperStar (ModuleCat.{u + 1} A) X)).symm

/-- The specified unbounded comparison: transpose the pullback-square identification
followed by the etale derived counit under the pro-etale derived adjunction.
All direct images are total right derived functors on K-injective resolutions.
Source: blueprint, sk-prop-pe-unbounded-classical-direct-image.md, displayed mate
(auxiliary; not a blueprint node). -/
noncomputable def unboundedDirectImageComparisonMap
    (A : Type (u + 1)) [CommRing A] {X Y : Scheme.{u}} (g : X ⟶ Y)
    (K : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) Y).mapDerivedCategory.obj
        ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj K) ⟶
      (ProEtale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj
        ((comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.obj K) :=
  ((ProEtale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction.homEquiv _ _)
    ((unboundedDirectImagePullbackIso A g).hom.app
        ((Etale.lowerStar (ModuleCat.{u + 1} A) g).rightDerivedFunctor.obj K) ≫
      (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory.map
        ((Etale.upperStarLowerStarAdjunction
          (ModuleCat.{u + 1} A) g).mapDerivedCategoryRightDerivedAdjunction.counit.app K))

end AlgebraicGeometry.ProEtale
