/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphDerivedIso
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange
public import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
public import WeilConjectures.AlgebraicGeometry.QuasiFiniteMorphismComparison
public import WeilConjectures.AlgebraicGeometry.UnboundedEtaleCompactSupportComparisons
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.CompConjugate
public import WeilConjectures.Compactification.Refinement
import WeilConjectures.Algebra.Category.ModuleCat.Presheaf.SheafificationBilinearExtension
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.Algebra.Homology.BoundedAboveFlatSheafKFlat
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
import WeilConjectures.Algebra.Homology.HomComplexComponents
import WeilConjectures.Algebra.Homology.HomTensorDegreewiseEquation
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import WeilConjectures.Algebra.Homology.OpenDerivedMatePresentation
import WeilConjectures.Algebra.Homology.QuasiIsoHomComplexMap
import WeilConjectures.Algebra.Homology.QuasiIsoSaturatedTriangulated
import WeilConjectures.Algebra.Homology.RhomIntoKInjectiveLocal
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import WeilConjectures.Algebra.Homology.TowerEvaluationKInjective
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModuleAdjunction
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.AlgebraicGeometry.ModuleSheavesColimitsForgetful
import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import WeilConjectures.AlgebraicGeometry.ProEtaleFiniteModules
import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.AlgebraicGeometry.ProfiniteTestObjectFunctor
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.AlgebraicGeometry.SfEtaleGraphProjectionArbitraryBase
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import WeilConjectures.CategoryTheory.DerivedCategory.DerivedAdjunctionCompatibility
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingClassEssentialConstancy
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.ShortExactPullback
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import WeilConjectures.CategoryTheory.LocalizedModuleAdjunctionExact
import WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.SheafPullbackForgetComparison
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresAbelian
import WeilConjectures.CategoryTheory.SiteCoveringAxioms
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimit
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.SixFunctors.Etale.Derived.HeartGluing
import WeilConjectures.SixFunctors.Etale.Derived.Perfect.SitePerfect
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction
import WeilConjectures.SixFunctors.ProEtale.BaseChange.WeaklyEtale
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.ModuleDerivedCategory
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.OpenLowerShriekProj
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.FlatModuleCat

/-! # Coherence of normalized etale sum right adjoints

proof.md, Step 1; Stacks Tags 03S6, 0F7J, 0F7K
(auxiliary; not a blueprint node).

The comparisons below use the actual proper/open compositor and exchange. The map to sum
extension is the constructed graph comparison, rather than a choice of a bare isomorphism.
Right adjoints and their adjunctions are quantified, so no choice of Brown adjoint is imposed.
-/

@[expose] public section

set_option autoImplicit false
universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] lowerStar upperStar etaleLowerShriek openImmersionLowerShriek
  Functor.mapDerivedCategory Functor.rightDerivedFunctor
  canonicalEtaleCompactSupportComparison derivedEtaleLowerShriekUpperStarAdjunction
  rightDerivedLowerShriekIso unboundedEtaleLowerShriekCompIso
  unboundedEtaleCompactSupportBaseChange exactEtaleSumExchange

/-- The specified compact-support-to-sum identification for the chosen compactification.
Source: Stacks Tags 0F4L, 0F7J, and the blueprint Step 1
(auxiliary; not a blueprint node). -/
noncomputable def etaleSumSupportIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    [HasCompactification e] :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ≅
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory :=
  (rightDerivedLowerShriekIso A (HasCompactification.compactification e)).symm ≪≫
    canonicalEtaleCompactSupportComparison A e (HasCompactification.compactification e)

/-- The normalization rho is the adjunction conjugate of the inverse specified comparison.
Source: blueprint Step 1; Stacks Tags 0037 and 03S6
(auxiliary; not a blueprint node). -/
noncomputable def etaleSumRightAdjointIso
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {U X : Scheme.{u}} (e : U ⟶ X) [Etale e] [IsSeparated e] [QuasiCompact e]
    [HasCompactification e]
    (G : DerivedCategoryModule A X ⥤ DerivedCategoryModule A U)
    (adj : rightDerivedLowerShriek (ModuleCat.{u + 1} A) e ⊣ G) :
    G ≅ (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory :=
  conjugateIsoEquiv adj
    (derivedEtaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e inferInstance)
    (etaleSumSupportIso A e).symm

/-- The canonical pullback identification of the coefficient unit, in the exact derived model.
Source: blueprint Step 1, pullback-unit identification
(auxiliary; not a blueprint node). -/
noncomputable def etaleSumPullbackUnitIso
    (A : Type (u + 1)) [CommRing A] {U X : Scheme.{u}} (e : U ⟶ X) :
    (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory.obj (constantComplex A X) ≅
      constantComplex A U :=
  (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) e).symm.app
      (constantComplex A X) ≪≫
    leftDerivedUpperStarUnitIso (ModuleCat.{u + 1} A) e

end AlgebraicGeometry.Etale
