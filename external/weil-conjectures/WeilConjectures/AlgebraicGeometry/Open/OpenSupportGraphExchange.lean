/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Open.OpenRestrictionCompactSupport
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

/-! # Cartesian exchange of the graph comparison between compactifications

## References

* Stacks Project, Tag 0F7F, the product-graph base-change calculation
-/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSimpArgs false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local irreducible] openRestrictionGraphIso sfGraphCompactificationComparison
  rightDerivedLowerShriekOfCompactificationBaseChangeMap'
  derivedOpenImmersionLowerShriekBaseChangeIso
  rightDerivedLowerShriekOfCompactificationBaseChangeMap

private theorem graph_eq_normalized
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c d : Compactification f) :
    openRestrictionGraphIso Λ c d =
      etaleGraphComparisonFromOpen Λ c (EtaleGraphPresentation.ofCompactification d) ≪≫
        etaleGraphOpenNormalization Λ d := by
  simp only [openRestrictionGraphIso, etaleGraphOpenNormalization,
    ← sfComparison_eq_graphComparison, Iso.trans_assoc]
  rfl

private theorem cartesian_exchange_transport
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {b : Y' ⟶ Y} (c : Compactification f) (d : Compactification f')
    (w : d.Z ⟶ c.Z) (hi : IsPullback v d.i c.i w) (hp : IsPullback w d.g c.g b) :
    compactificationExactExchange Λ c d w hi hp =
      Functor.whiskerLeft Rf_!(c)[ModuleCat.{u + 1} Λ]
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) b).inv ≫
        rightDerivedLowerShriekOfCompactificationBaseChangeMap'
          (ModuleCat.{u + 1} Λ) c d w hi hp.toCommSq ≫
        Functor.whiskerRight
          (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} Λ) v).hom
          Rf_!(d)[ModuleCat.{u + 1} Λ] := by
  ext M
  have h := congr_app (exact_exchange_transport Λ hp.toCommSq)
    (D((c.i)_!open[ModuleCat.{u + 1} Λ]).obj M)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app] at h
  simp only [compactificationExactExchange, rightDerivedLowerShriekOfCompactificationBaseChangeMap',
    derivedOpenImmersionLowerShriekBaseChangeIso,
    Iso.trans_inv, Iso.symm_inv, Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv,
    NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.map_comp, Category.assoc, Category.id_comp, Category.comp_id]
  rw [← h]
  dsimp only [rightDerivedLowerShriekOfCompactification, Functor.comp_map, Functor.comp_obj]
  simp only [Functor.map_comp, Category.assoc]
  simp only [← Functor.map_comp_assoc, ← Functor.map_comp, Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

/-- The graph factor alone commutes with Cartesian compactification exchange. -/
theorem openRestrictionGraphIso_cartesianExchange
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y} {f' : X' ⟶ Y'}
    {v : X' ⟶ X} {b : Y' ⟶ Y} (sq : IsPullback v f' f b)
    (c d : Compactification f) (d' : Compactification f')
    (w : d'.Z ⟶ d.Z) (hi : IsPullback v d'.i d.i w)
    (hp : IsPullback w d'.g d.g b) :
    Functor.whiskerRight (openRestrictionGraphIso Λ c d).hom
        L((b)^*[ModuleCat.{u + 1} Λ]) ≫
      rightDerivedLowerShriekOfCompactificationBaseChangeMap'
        (ModuleCat.{u + 1} Λ) d d' w hi hp.toCommSq =
    rightDerivedLowerShriekOfCompactificationBaseChangeMap (ModuleCat.{u + 1} Λ) sq c ≫
      Functor.whiskerLeft L((v)^*[ModuleCat.{u + 1} Λ])
        (openRestrictionGraphIso Λ (c.ofIsPullback sq) d').hom := by
  let A := ModuleCat.{u + 1} Λ
  have h := graphComparisonFromOpen_exchange Λ c sq
    (EtaleGraphPresentation.ofCompactification d)
    (EtaleGraphPresentation.ofCompactification d')
    (compactificationPresentationBaseChange d d' w hi hp)
  have hn := graphOpenNormalization_exchange Λ d d' w hi hp
  have hd (M : DerivedCategoryModule Λ X) :
      D((b)^*[A]).map ((openRestrictionGraphIso Λ c d).hom.app M) ≫
        (compactificationExactExchange Λ d d' w hi hp).app M =
      (compactificationExactExchange Λ c (c.ofIsPullback sq)
          (pullback.fst c.g b) (c.isPullback_i_ofIsPullback sq)
          (c.isPullback_g_ofIsPullback sq).flip).app M ≫
        (openRestrictionGraphIso Λ (c.ofIsPullback sq) d').hom.app
          (D((v)^*[A]).obj M) := by
    simp only [graph_eq_normalized, Iso.trans_hom, NatTrans.comp_app,
      Functor.map_comp, Category.assoc]
    rw [hn M, ← Category.assoc, h M, Category.assoc]
  ext M
  have H := hd M
  rw [cartesian_exchange_transport Λ d d' w hi hp,
    compactificationExactExchange_transport Λ c sq] at H
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.comp_obj, Category.assoc] at H ⊢
  have hb := (leftDerivedUpperStarIsoMapDerivedCategory A b).inv.naturality
    ((openRestrictionGraphIso Λ c d).hom.app M)
  have hv := (openRestrictionGraphIso Λ (c.ofIsPullback sq) d').hom.naturality
    ((leftDerivedUpperStarIsoMapDerivedCategory A v).hom.app M)
  simp only [Functor.comp_obj] at hv
  rw [reassoc_of% hb, hv] at H
  apply (cancel_mono (Rf_!(d')[A].map
    ((leftDerivedUpperStarIsoMapDerivedCategory A v).hom.app M))).1
  simpa only [Category.assoc] using
    ((cancel_epi ((leftDerivedUpperStarIsoMapDerivedCategory A b).inv.app
        (Rf_!(c)[A].obj M))).1 H)

end AlgebraicGeometry.Etale
