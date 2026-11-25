/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Open.OpenSupportFactorModel
public import WeilConjectures.AlgebraicGeometry.Open.OpenSupportCompactificationModel
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import all WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportCompositionBaseChange
import all WeilConjectures.AlgebraicGeometry.SfGraphCompactSupportComposition
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import all WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChange
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonInterchange
import all WeilConjectures.AlgebraicGeometry.EtaleGraphInterchangeData
import all WeilConjectures.AlgebraicGeometry.DerivedCategories
import all WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import all Mathlib.AlgebraicGeometry.Morphisms.Proper
import all Mathlib.AlgebraicGeometry.OpenImmersion
import all WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import all WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import all Mathlib.CategoryTheory.Functor.Derived.RightDerived
import all WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import all WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import all Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import all Mathlib.Algebra.Homology.DerivedCategory.Fractions
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all WeilConjectures.CategoryTheory.GeometricModuleConstruction
import all WeilConjectures.CategoryTheory.RingedToposRingData
import all WeilConjectures.CategoryTheory.AdjunctionRingOperations
import all Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import all Mathlib.CategoryTheory.Adjunction.Basic
import all Mathlib.CategoryTheory.Sites.CartesianMonoidal
import all Mathlib.CategoryTheory.Monoidal.CommGrp_
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import all WeilConjectures.CategoryTheory.GeometricModuleTransport
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import all Mathlib.CategoryTheory.Adjunction.Limits
import all WeilConjectures.CategoryTheory.GeometricRingTransport
import all Mathlib.CategoryTheory.Sites.Limits
import all WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import all WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import all WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import all WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import all Mathlib.CategoryTheory.Limits.ExactFunctor
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import all Mathlib.Algebra.Homology.HomologicalComplex
import all Mathlib.Algebra.Homology.Additive
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import all WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import all Mathlib.CategoryTheory.Types.Basic
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import all WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import all Mathlib.LinearAlgebra.TensorProduct.Vanishing
import all Mathlib.RingTheory.TensorProduct.DirectLimitFG
import all Mathlib.LinearAlgebra.TensorProduct.Finiteness
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import all Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import all WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import all Mathlib.CategoryTheory.Sites.Sheaf
import all Mathlib.CategoryTheory.Sites.LocallyBijective
import all Mathlib.CategoryTheory.Limits.Types.Pullbacks
import all Mathlib.CategoryTheory.Functor.EpiMono
import all Mathlib.CategoryTheory.Limits.Types.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import all Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import all Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import all WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import all WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import all Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import all Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import all WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import all WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import all Mathlib.CategoryTheory.Sites.PreservesSheafification
import all Mathlib.CategoryTheory.Limits.Preserves.Limits
import all WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import all Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import all Mathlib.RingTheory.Flat.CategoryTheory
import all Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import all Mathlib.Algebra.Homology.Embedding.CochainComplex
import all Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import all Mathlib.Algebra.Category.Grp.AB
import all WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import all WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Preadditive
import all WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import all Mathlib.CategoryTheory.Monoidal.Closed.Basic
import all WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import all WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import all Mathlib.CategoryTheory.Adjunction.CompositionIso
import all WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
import all WeilConjectures.SixFunctors.EtaleLocallyClosedGraphModel
import all Mathlib.AlgebraicGeometry.Scheme
import all Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import all WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import all WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import all WeilConjectures.SixFunctors.BaseChange.Square
import all WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import all WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import all WeilConjectures.AlgebraicGeometry.EtaleProperOpenExchangeCube
import all WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import all WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import all WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import all WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
import all WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import all WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import all WeilConjectures.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization
import all Mathlib.AlgebraicGeometry.Sites.Etale
import all WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import all WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import all WeilConjectures.AlgebraicGeometry.EtaleSheaves
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import all Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import all Mathlib.CategoryTheory.Sites.Point.Basic
import all Mathlib.AlgebraicGeometry.Sites.EtalePoint
import all WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import all WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import all WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import all Mathlib.CategoryTheory.Sites.Subsheaf
import all WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import all WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import all WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import all WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import all WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import all Mathlib.AlgebraicGeometry.Morphisms.Etale
import all Mathlib.AlgebraicGeometry.Pullbacks
import all WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import all WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import all Mathlib.AlgebraicGeometry.Sites.Fpqc
import all WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import all WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import all Mathlib.AlgebraicGeometry.PullbackCarrier
import all WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import all WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
import all WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import all WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import all WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import all WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
import all WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
import all WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
import all WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
import all WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import all WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import all WeilConjectures.Compactification.NagataCompactification
import all WeilConjectures.Compactification.Defs
import all WeilConjectures.SixFunctors.OpenClosed.Complex
import all WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
import all Mathlib.FieldTheory.IsAlgClosed.Basic
import all WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
import all WeilConjectures.Mathlib.RingTheory.Henselian
import all WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import all WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import all WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import all WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import all Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import all Mathlib.AlgebraicGeometry.ResidueField
import all Mathlib.FieldTheory.IsSepClosed
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import all WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import all WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import all WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import all WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import all WeilConjectures.RingTheory.StrictHenselizationTriples
import all WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import all WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import all WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import all WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import all WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import all WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import all WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMaps
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import all WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
import all WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import all WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
import all WeilConjectures.Compactification.BaseChange
import all Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import all WeilConjectures.SixFunctors.OpenClosed.Exact
import all WeilConjectures.SixFunctors.BaseChange.Pasting
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.AlgebraicGeometry.EtaleProperOpenCartesianNormalization
import all WeilConjectures.AlgebraicGeometry.Derived.DerivedExchangeModuleTermwiseSupplement
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenCompositionSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleProperOpenCubeNormalization
import all WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenInterchangeSupplement
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenPastingSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkSidePasting
import all WeilConjectures.AlgebraicGeometry.EtaleGraphNeighborhoodWords
import all WeilConjectures.AlgebraicGeometry.EtaleGraphNeighborhoodGeometry
import all WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonOpenShrink
import all WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkMiddlePasting
import all WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkFirstLeg
import all WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkIntersectionWords
import all WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphMiddleTransport
import all WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphTransport
import all WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkSecondLeg
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductRowPasting
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductInterchange
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductGeometry
import all WeilConjectures.AlgebraicGeometry.EtalePairwiseProductGraphNormalization
import all WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonProperAmbient
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientFirstSide
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientData
import all WeilConjectures.AlgebraicGeometry.EtaleProperAmbientTransportComposition
import all WeilConjectures.AlgebraicGeometry.Derived.DerivedCompactSupportCompositionCoherenceSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientSecondSide
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientMiddle
import all WeilConjectures.AlgebraicGeometry.SfExactExchangePasting
import all WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkPasting
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductAmbientPasting
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductAmbientGeometry
import all WeilConjectures.AlgebraicGeometry.EtaleGraphAmbientSourcePasting
import all WeilConjectures.AlgebraicGeometry.Open.OpenExchangeTowerSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleGraphAmbientSquarePasting
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkLift
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkWords
import all WeilConjectures.AlgebraicGeometry.EtaleGraphProductShrinkSquare
import all WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonBaseChange
import all WeilConjectures.AlgebraicGeometry.EtaleGraphDiagonalNormalization
import all WeilConjectures.AlgebraicGeometry.EtaleGraphRefinementNormalization
import all WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphSideTransport
import all WeilConjectures.AlgebraicGeometry.EtaleGraphFromOpenBaseChange
import all WeilConjectures.AlgebraicGeometry.Open.OpenSupportGraphExchange

/-! # The graph-free proper/open part of the support cube
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] Functor.mapDerivedCategory Functor.rightDerivedFunctor
  Functor.leftDerivedFunctor lowerStar upperStar openImmersionLowerShriek
  mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
  mapDerivedCategoryOpenImmersionLowerShriekComp openSupportTailIso
  compactificationExactExchange compactificationSupportBaseChangeIso
  derivedOpenImmersionLowerShriekBaseChangeIso
  rightDerivedLowerShriekOfCompactificationBaseChangeMap'
  rightDerivedLowerShriekOfCompactificationBaseChangeMap
  openImmersionLowerShriekLowerStarExchange exactDerivedBaseChangeMap

private theorem open_exchange_congr
    (Λ : Type (u + 1)) [CommRing Λ]
    {V V' Z Z' : Scheme.{u}} {b : V' ⟶ V} {z : Z' ⟶ Z}
    {r s : V ⟶ Z} {r' s' : V' ⟶ Z'}
    [IsOpenImmersion r] [IsOpenImmersion s]
    [IsOpenImmersion r'] [IsOpenImmersion s']
    (hr : r = s) (hr' : r' = s')
    (sq : IsPullback b r' r z) (sq' : IsPullback b s' s z)
    (K : DerivedCategoryModule Λ V) :
    D((z)^*[ModuleCat.{u + 1} Λ]).map
        ((mapDerivedCategoryOpenImmersionLowerShriekCongr
          (ModuleCat.{u + 1} Λ) hr).hom.app K) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} Λ) sq').inv.app K =
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} Λ) sq).inv.app K ≫
      (mapDerivedCategoryOpenImmersionLowerShriekCongr
        (ModuleCat.{u + 1} Λ) hr').hom.app
        (D((b)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  subst s s'
  simp only [mapDerivedCategoryOpenImmersionLowerShriekCongr,
    Iso.refl_hom, NatTrans.id_app, CategoryTheory.Functor.map_id,
    Category.id_comp, Category.comp_id]
  exact (Category.comp_id
    ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} Λ) sq).inv.app K)).symm

private noncomputable def openWordIso
    (A : Type (u + 2)) [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {V P X Z : Scheme.{u}}
    (i : V ⟶ P) (k : P ⟶ Z) (a : V ⟶ X) (t : X ⟶ Z)
    [IsOpenImmersion i] [IsOpenImmersion k]
    [IsOpenImmersion a] [IsOpenImmersion t]
    (h : i ≫ k = a ≫ t) :
    D((i)_!open[A]) ⋙ D((k)_!open[A]) ≅ D((a)_!open[A]) ⋙ D((t)_!open[A]) :=
  (mapDerivedCategoryOpenImmersionLowerShriekComp A i k).symm ≪≫
    mapDerivedCategoryOpenImmersionLowerShriekCongr A h ≪≫
      mapDerivedCategoryOpenImmersionLowerShriekComp A a t

private theorem openWord_exchange
    (Λ : Type (u + 1)) [CommRing Λ]
    {V V' P P' X X' Z Z' : Scheme.{u}}
    {b : V' ⟶ V} {w : P' ⟶ P} {g' : X' ⟶ X} {z : Z' ⟶ Z}
    {i : V ⟶ P} {k : P ⟶ Z} {a : V ⟶ X} {t : X ⟶ Z}
    {i' : V' ⟶ P'} {k' : P' ⟶ Z'} {a' : V' ⟶ X'} {t' : X' ⟶ Z'}
    [IsOpenImmersion i] [IsOpenImmersion k]
    [IsOpenImmersion a] [IsOpenImmersion t]
    [IsOpenImmersion i'] [IsOpenImmersion k']
    [IsOpenImmersion a'] [IsOpenImmersion t']
    (sqI : IsPullback b i' i w) (sqK : IsPullback w k' k z)
    (sqA : IsPullback b a' a g') (sqT : IsPullback g' t' t z)
    (h : i ≫ k = a ≫ t) (h' : i' ≫ k' = a' ≫ t')
    (K : DerivedCategoryModule Λ V) :
    D((z)^*[ModuleCat.{u + 1} Λ]).map
        ((openWordIso (ModuleCat.{u + 1} Λ) i k a t h).hom.app K) ≫
      (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} Λ) sqT).inv.app (D((a)_!open[ModuleCat.{u + 1} Λ]).obj K) ≫
      D((t')_!open[ModuleCat.{u + 1} Λ]).map
        ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} Λ) sqA).inv.app K) =
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} Λ) sqK).inv.app (D((i)_!open[ModuleCat.{u + 1} Λ]).obj K) ≫
      D((k')_!open[ModuleCat.{u + 1} Λ]).map
        ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} Λ) sqI).inv.app K) ≫
      (openWordIso (ModuleCat.{u + 1} Λ) i' k' a' t' h').hom.app
        (D((b)^*[ModuleCat.{u + 1} Λ]).obj K) := by
  let A := ModuleCat.{u + 1} Λ
  have hI := sfExactExchangePasting.2.2 Λ sqI sqK K
  have hA := sfExactExchangePasting.2.2 Λ sqA sqT K
  have hC := open_exchange_congr Λ h h' (sqI.paste_vert sqK) (sqA.paste_vert sqT) K
  simp only [openWordIso, Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app,
    Functor.map_comp, Category.assoc]
  apply (cancel_mono ((mapDerivedCategoryOpenImmersionLowerShriekComp A a' t').inv.app
    (D((b)^*[A]).obj K))).1
  dsimp only [A]
  simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  rw [← hA]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  rw [hC, reassoc_of% hI]

private theorem properOpen_cube_forward
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {P Z U Y P' Z' U' Y' : Scheme.{u}}
    {k : P ⟶ Z} {r : P ⟶ U} {p : Z ⟶ Y} {j : U ⟶ Y}
    {k' : P' ⟶ Z'} {r' : P' ⟶ U'} {p' : Z' ⟶ Y'} {j' : U' ⟶ Y'}
    {w : P' ⟶ P} {z : Z' ⟶ Z} {c : U' ⟶ U} {g : Y' ⟶ Y}
    [IsOpenImmersion k] [IsOpenImmersion j]
    [IsOpenImmersion k'] [IsOpenImmersion j']
    [IsProper r] [IsProper p] [IsProper r'] [IsProper p']
    (sq : IsPullback r k j p) (sq' : IsPullback r' k' j' p')
    (sqK : IsPullback w k' k z) (sqJ : IsPullback c j' j g)
    (sqP : IsPullback z p' p g) (sqR : IsPullback w r' r c)
    (M : DerivedCategoryModule Λ P) :
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} Λ) sqJ).hom.app (R((r)_*[ModuleCat.{u + 1} Λ]).obj M) ≫
      D((g)^*[ModuleCat.{u + 1} Λ]).map
        ((openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ) sq).app M) ≫
      (exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqP.toCommSq).app
        (D((k)_!open[ModuleCat.{u + 1} Λ]).obj M) =
    D((j')_!open[ModuleCat.{u + 1} Λ]).map
        ((exactDerivedBaseChangeMap (ModuleCat.{u + 1} Λ) sqR.toCommSq).app M) ≫
      (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ) sq').app
        (D((w)^*[ModuleCat.{u + 1} Λ]).obj M) ≫
      R((p')_*[ModuleCat.{u + 1} Λ]).map
        ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} Λ) sqK).hom.app M) := by
  obtain ⟨_θ, _Γ, _hθ, _hΓ, hCart, _hVert, _hHoriz, _hIdV, _hIdH, hCube⟩ :=
    etaleProperOpenExchangeCube Λ
  have H := congr_app (hCube k r p j k' r' p' j' w z c g
    sq.toCommSq.flip sq'.toCommSq.flip sqK sqJ sqP sqR) M
  rw [hCart k r p j sq, hCart k' r' p' j' sq'] at H
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id, Category.assoc] at H
  have H' := congrArg (fun q =>
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
      (ModuleCat.{u + 1} Λ) sqJ).hom.app (R((r)_*[ModuleCat.{u + 1} Λ]).obj M) ≫
    q ≫ R((p')_*[ModuleCat.{u + 1} Λ]).map
      ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} Λ) sqK).hom.app M)) H
  simpa only [Functor.comp_obj, Category.assoc, ← Functor.map_comp, ← Functor.map_comp_assoc,
    Iso.inv_hom_id_app, Iso.hom_inv_id_app_assoc, CategoryTheory.Functor.map_id,
    Category.comp_id, Category.id_comp] using H'

private theorem tail_hom
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y} {j : U ⟶ Y} [IsOpenImmersion j]
    {a : V ⟶ X} [IsOpenImmersion a] {p : V ⟶ U}
    (sq : IsPullback a p f j) (cf : Compactification f)
    (K : DerivedCategoryModule Λ V) :
    (openSupportTailIso Λ sq cf).hom.app K =
      (openImmersionLowerShriekLowerStarExchange (ModuleCat.{u + 1} Λ)
        (IsPullback.of_hasPullback cf.g j).flip).app
        (D(((cf.ofIsPullback sq).i)_!open[ModuleCat.{u + 1} Λ]).obj K) ≫
      R((cf.g)_*[ModuleCat.{u + 1} Λ]).map
        ((openWordIso (ModuleCat.{u + 1} Λ) (cf.ofIsPullback sq).i
          (pullback.fst cf.g j) a cf.i (cf.ofIsPullback_i_fst sq)).hom.app K) := by
  simp only [openSupportTailIso, openWordIso,
    openImmersionLowerShriekLowerStarExchangeIso, asIso_hom,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_inv,
    Functor.isoWhiskerLeft_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Category.assoc, Category.id_comp, Category.comp_id]

private theorem tail_exact
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' U V U' V' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g)
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sqU : IsPullback a p f j)
    {c : U' ⟶ U} {j' : U' ⟶ Y'} [IsOpenImmersion j']
    (sqj : IsPullback c j' j g)
    {b : V' ⟶ V} {p' : V' ⟶ U'} (_sq' : IsPullback b p' p c)
    {a' : V' ⟶ X'} [IsOpenImmersion a'] (sqV : IsPullback a' p' f' j')
    (sqA : IsPullback b a' a g') (cf : Compactification f)
    (w : ((cf.ofIsPullback sq).ofIsPullback sqV).Z ⟶ (cf.ofIsPullback sqU).Z)
    (hi : IsPullback b ((cf.ofIsPullback sq).ofIsPullback sqV).i
      (cf.ofIsPullback sqU).i w)
    (hp : IsPullback w ((cf.ofIsPullback sq).ofIsPullback sqV).g
      (cf.ofIsPullback sqU).g c)
    (hw : w ≫ pullback.fst cf.g j =
      pullback.fst (cf.ofIsPullback sq).g j' ≫ pullback.fst cf.g g)
    (K : DerivedCategoryModule Λ V) :
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
        (ModuleCat.{u + 1} Λ) sqj).hom.app
        (Rf_!(cf.ofIsPullback sqU)[ModuleCat.{u + 1} Λ].obj K) ≫
      D((g)^*[ModuleCat.{u + 1} Λ]).map ((openSupportTailIso Λ sqU cf).hom.app K) ≫
      (compactificationExactExchange Λ cf (cf.ofIsPullback sq)
        (pullback.fst cf.g g) (cf.isPullback_i_ofIsPullback sq)
        (cf.isPullback_g_ofIsPullback sq).flip).app
        (D((a)_!open[ModuleCat.{u + 1} Λ]).obj K) =
    D((j')_!open[ModuleCat.{u + 1} Λ]).map
        ((compactificationExactExchange Λ (cf.ofIsPullback sqU)
          ((cf.ofIsPullback sq).ofIsPullback sqV) w hi hp).app K) ≫
      (openSupportTailIso Λ sqV (cf.ofIsPullback sq)).hom.app
        (D((b)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      Rf_!(cf.ofIsPullback sq)[ModuleCat.{u + 1} Λ].map
        ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso
          (ModuleCat.{u + 1} Λ) sqA).hom.app K) := by
  let A := ModuleCat.{u + 1} Λ
  let df := cf.ofIsPullback sq
  let cq := cf.ofIsPullback sqU
  let dq := df.ofIsPullback sqV
  let k := pullback.fst cf.g j
  let k' := pullback.fst df.g j'
  let z := pullback.fst cf.g g
  let si := cf.isPullback_i_ofIsPullback sq
  let sp := (cf.isPullback_g_ofIsPullback sq).flip
  have hk : k ≫ cf.g = cq.g ≫ j := pullback.condition
  have hk' : k' ≫ df.g = dq.g ≫ j' := pullback.condition
  have sqK : IsPullback w k' k z := by
    apply IsPullback.of_bot (p := hw) (t := sp)
    rw [hk, hk']
    exact hp.paste_vert sqj
  let H := openWordIso A cq.i k a cf.i (cf.ofIsPullback_i_fst sqU)
  have hC := properOpen_cube_forward Λ
    (IsPullback.of_hasPullback cf.g j).flip
    (IsPullback.of_hasPullback df.g j').flip sqK sqj sp hp
    (D((cq.i)_!open[A]).obj K)
  have hP := (exactDerivedBaseChangeMap A sp.toCommSq).naturality (H.hom.app K)
  have hN := (openImmersionLowerShriekLowerStarExchange A
    (IsPullback.of_hasPullback df.g j').flip).naturality
      ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A hi).inv.app K)
  have hO := openWord_exchange Λ hi sqK sqA si
    (cf.ofIsPullback_i_fst sqU) (df.ofIsPullback_i_fst sqV) K
  have hOmixed := congrArg (fun q =>
    (mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A sqK).hom.app
      (D((cq.i)_!open[A]).obj K) ≫ q ≫ D((df.i)_!open[A]).map
      ((mapDerivedCategoryOpenImmersionLowerShriekBaseChangeIso A sqA).hom.app K)) hO
  dsimp only [A, df, cq, dq] at hOmixed
  simp only [Category.assoc, ← Functor.map_comp_assoc, ← Functor.map_comp,
    Iso.inv_hom_id_app, Iso.hom_inv_id_app_assoc, CategoryTheory.Functor.map_id,
    Functor.comp_obj, Category.id_comp, Category.comp_id] at hOmixed
  have hM := congrArg (R((df.g)_*[A]).map) hOmixed
  simp only [Functor.map_comp, Category.assoc] at hM
  simp only [Functor.comp_obj, Functor.comp_map] at hP hN
  rw [tail_hom, tail_hom]
  dsimp only [A, df, cq, dq, k, k', z, si, sp, H]
    at hP hN hC hM ⊢
  simp only [compactificationExactExchange, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Category.assoc, Category.id_comp, Category.comp_id]
  dsimp only [rightDerivedLowerShriekOfCompactification, rightDerivedLowerStar,
    Functor.comp_obj, Functor.comp_map] at hP hN hC hM ⊢
  erw [reassoc_of% hP, reassoc_of% hC, hM, ← reassoc_of% hN]
  rfl

/-- The proper/open interchange and open compositor commute with base change. -/
theorem openSupportTail_cube
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' U V U' V' : Scheme.{u}}
    {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'} {g' : X' ⟶ X}
    (sq : IsPullback g' f' f g)
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sqU : IsPullback a p f j)
    {c : U' ⟶ U} {j' : U' ⟶ Y'} [IsOpenImmersion j']
    (sqj : IsPullback c j' j g)
    {b : V' ⟶ V} {p' : V' ⟶ U'} (sq' : IsPullback b p' p c)
    {a' : V' ⟶ X'} [IsOpenImmersion a'] (sqV : IsPullback a' p' f' j')
    (sqA : IsPullback b a' a g') (cf : Compactification f)
    (w : ((cf.ofIsPullback sq).ofIsPullback sqV).Z ⟶ (cf.ofIsPullback sqU).Z)
    (hi : IsPullback b ((cf.ofIsPullback sq).ofIsPullback sqV).i
      (cf.ofIsPullback sqU).i w)
    (hp : IsPullback w ((cf.ofIsPullback sq).ofIsPullback sqV).g
      (cf.ofIsPullback sqU).g c)
    (hw : w ≫ pullback.fst cf.g j =
      pullback.fst (cf.ofIsPullback sq).g j' ≫ pullback.fst cf.g g)
    (K : DerivedCategoryModule Λ V) :
    (derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sqj).hom.app
        (Rf_!(cf.ofIsPullback sqU)[ModuleCat.{u + 1} Λ].obj K) ≫
      L((g)^*[ModuleCat.{u + 1} Λ]).map ((openSupportTailIso Λ sqU cf).hom.app K) ≫
      (compactificationSupportBaseChangeIso Λ sq cf).hom.app
        (D((a)_!open[ModuleCat.{u + 1} Λ]).obj K) =
    D((j')_!open[ModuleCat.{u + 1} Λ]).map
        ((rightDerivedLowerShriekOfCompactificationBaseChangeMap'
          (ModuleCat.{u + 1} Λ) (cf.ofIsPullback sqU)
          ((cf.ofIsPullback sq).ofIsPullback sqV) w hi hp.toCommSq).app K) ≫
      (openSupportTailIso Λ sqV (cf.ofIsPullback sq)).hom.app
        (L((b)^*[ModuleCat.{u + 1} Λ]).obj K) ≫
      Rf_!(cf.ofIsPullback sq)[ModuleCat.{u + 1} Λ].map
        ((derivedOpenImmersionLowerShriekBaseChangeIso (ModuleCat.{u + 1} Λ) sqA).hom.app K)
    := by
  let A := ModuleCat.{u + 1} Λ
  let df := cf.ofIsPullback sq
  let cq := cf.ofIsPullback sqU
  let dq := df.ofIsPullback sqV
  have Hd := tail_exact Λ sq sqU sqj sq' sqV sqA cf w hi hp hw K
  have hcf := congr_app (compactificationExactExchange_transport Λ cf sq)
    (D((a)_!open[A]).obj K)
  have hcq := congr_app (cartesian_exchange_transport Λ cq dq w hi hp) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    at hcf hcq
  have Hg := (leftDerivedUpperStarIsoMapDerivedCategory A g).inv.naturality
    ((openSupportTailIso Λ sqU cf).hom.app K)
  have HT := (openSupportTailIso Λ sqV df).hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory A b).hom.app K)
  apply (cancel_epi (D((j')_!open[A]).map
    ((leftDerivedUpperStarIsoMapDerivedCategory A c).inv.app (Rf_!(cq)[A].obj K)))).1
  apply (cancel_mono (Rf_!(df)[A].map
    ((leftDerivedUpperStarIsoMapDerivedCategory A g').hom.app
      (D((a)_!open[A]).obj K)))).1
  dsimp only [A, df, cq, dq] at Hg HT hcf hcq Hd ⊢
  simp only [derivedOpenImmersionLowerShriekBaseChangeIso,
    Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [rightDerivedLowerShriekOfCompactification, rightDerivedLowerStar,
    Functor.comp_obj, Functor.comp_map] at Hg HT hcf hcq Hd ⊢
  rw [← reassoc_of% Hg, ← reassoc_of% HT]
  simp only [compactificationSupportBaseChangeIso, asIso_hom]
  rw [← hcf]
  have hcqJ := congrArg (D((j')_!open[A]).map) hcq
  simp only [Functor.map_comp, Category.assoc] at hcqJ
  rw [← reassoc_of% hcqJ]
  dsimp only [A]
  simp only [CategoryTheory.Functor.map_id, Category.comp_id]
  exact Hd

end AlgebraicGeometry.Etale
