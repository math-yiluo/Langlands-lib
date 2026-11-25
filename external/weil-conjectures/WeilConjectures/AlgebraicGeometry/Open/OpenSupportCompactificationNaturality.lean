/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Open.OpenSupportCompactificationModel
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonBaseChange
import WeilConjectures.AlgebraicGeometry.EtaleGraphPresentation
import WeilConjectures.SixFunctors.EtaleLocallyClosedGraphModel
import Mathlib.AlgebraicGeometry.Scheme
import Mathlib.AlgebraicGeometry.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekComposition
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekIndependenceUnbounded
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.AlgebraicGeometry.EtaleGraphDiagonalNormalization
import WeilConjectures.AlgebraicGeometry.EtaleGraphRefinementNormalization
import WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphMiddleTransport
import WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphTransport
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenExchangeCube
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjection
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekLowerStarExchange
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
import WeilConjectures.CategoryTheory.K.KInjectiveTotalDerived
import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.RightDerived
import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
import Mathlib.Algebra.Homology.DerivedCategory.Fractions
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import WeilConjectures.CategoryTheory.GeometricModuleConstruction
import WeilConjectures.CategoryTheory.RingedToposRingData
import WeilConjectures.CategoryTheory.AdjunctionRingOperations
import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Sites.CartesianMonoidal
import Mathlib.CategoryTheory.Monoidal.CommGrp_
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
import WeilConjectures.CategoryTheory.GeometricModuleTransport
import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GeometricRingTransport
import Mathlib.CategoryTheory.Sites.Limits
import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
import Mathlib.CategoryTheory.Limits.ExactFunctor
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.Algebra.Homology.Additive
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
import Mathlib.CategoryTheory.Types.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
import Mathlib.LinearAlgebra.TensorProduct.Vanishing
import Mathlib.RingTheory.TensorProduct.DirectLimitFG
import Mathlib.LinearAlgebra.TensorProduct.Finiteness
import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
import Mathlib.CategoryTheory.Sites.Sheaf
import Mathlib.CategoryTheory.Sites.LocallyBijective
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.Limits.Types.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import Mathlib.CategoryTheory.Sites.PreservesSheafification
import Mathlib.CategoryTheory.Limits.Preserves.Limits
import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
import Mathlib.RingTheory.Flat.CategoryTheory
import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
import Mathlib.Algebra.Category.Grp.AB
import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Preadditive
import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Comp
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.CategoryTheory.Adjunction.CompositionIso
import WeilConjectures.SixFunctors.Etale.LowerShriek.Comparison
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenHorizontalNormalization
import Mathlib.AlgebraicGeometry.Sites.Etale
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.AlgebraicGeometry.ProperSupportSheafComposition
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.AlgebraicGeometry.ReducedInducedClosedSubscheme
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.CategoryTheory.Sites.Point.Basic
import Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionCalculus
import WeilConjectures.AlgebraicGeometry.EtaleSectionProperSupport
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Stalk
import Mathlib.CategoryTheory.Sites.Subsheaf
import WeilConjectures.AlgebraicGeometry.EtaleModuleSectionClosedSupport
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.EtaleCohomology.EtaleSectionZeroOpen
import WeilConjectures.AlgebraicGeometry.EtaleSectionsEqualOpenEtaleCriterion
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionLocality
import WeilConjectures.AlgebraicGeometry.ClosedProperSupportLocality
import Mathlib.AlgebraicGeometry.Morphisms.Etale
import Mathlib.AlgebraicGeometry.Pullbacks
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseProperties
import WeilConjectures.AlgebraicGeometry.Morphisms.FpqcDescent
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.ProperMorphismFpqcDescent
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Fpqc
import WeilConjectures.AlgebraicGeometry.FieldExtensionDescent
import Mathlib.AlgebraicGeometry.PullbackCarrier
import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBaseUnionPreimage
import WeilConjectures.AlgebraicGeometry.ProperSupportCompositeRange
import WeilConjectures.AlgebraicGeometry.ProperSupportSectionImage
import WeilConjectures.AlgebraicGeometry.OpenExtensionProperSupportRange
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.FiniteComparison
import WeilConjectures.AlgebraicGeometry.ProperSupportExchangeRange
import WeilConjectures.SecSmoothPurity.ProperSupportFibreRestrictionCompatibility
import WeilConjectures.SecSmoothPurity.ProperSupportPullbackSectionMap
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalk
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeGerms
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.GlobalSections
import WeilConjectures.AlgebraicGeometry.InverseImageStalkGerm
import WeilConjectures.Compactification.NagataCompactification
import WeilConjectures.Compactification.Defs
import WeilConjectures.SixFunctors.OpenClosed.Complex
import WeilConjectures.AlgebraicGeometry.ProperGeometricPointExchange
import Mathlib.FieldTheory.IsAlgClosed.Basic
import WeilConjectures.AlgebraicGeometry.ProperStrictLocalFibreSections
import WeilConjectures.Mathlib.RingTheory.Henselian
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.DegreeZero
import WeilConjectures.AlgebraicGeometry.EtaleSectionsBaseFieldExtension
import WeilConjectures.AlgebraicGeometry.EtaleModuleSetPullbackComparison
import WeilConjectures.AlgebraicGeometry.QcqsGeometricExchangeFactorization
import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationExtension
import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
import WeilConjectures.AlgebraicGeometry.StrictHenselizationFunctoriality
import Mathlib.AlgebraicGeometry.ResidueField
import Mathlib.FieldTheory.IsSepClosed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationLocalStructure
import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointedMap
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationPointed
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluation
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationProperties
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationImage
import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import WeilConjectures.AlgebraicGeometry.StrictHenselizationPointEvaluationComparison
import WeilConjectures.AlgebraicGeometry.EtaleResidueTriples
import WeilConjectures.AlgebraicGeometry.EtaleLocalRingTriples
import WeilConjectures.RingTheory.StrictHenselizationTriples
import WeilConjectures.AlgebraicGeometry.EtalePointedMapRigidity
import WeilConjectures.AlgebraicGeometry.StrictHenselizationMapExists
import WeilConjectures.AlgebraicGeometry.QcqsStrictLocalModuleComparison
import WeilConjectures.AlgebraicGeometry.GeometricFibreExchangeRepresentative
import WeilConjectures.AlgebraicGeometry.EtaleUnitSectionRestriction
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.SetsPushforwardStalkStrictHenselization
import WeilConjectures.AlgebraicGeometry.SmallStrictLocalSectionMaps
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointPullbackStalk
import WeilConjectures.AlgebraicGeometry.Geometric.GeometricPointCanonicalGerm
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.BaseChangeSquare
import WeilConjectures.AlgebraicGeometry.ProperSupportGeometricStalkCore
import WeilConjectures.Compactification.BaseChange
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import WeilConjectures.SixFunctors.OpenClosed.Exact
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenCartesianNormalization
import WeilConjectures.AlgebraicGeometry.Derived.DerivedExchangeModuleTermwiseSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenCompositionSupplement
import WeilConjectures.AlgebraicGeometry.EtaleProperOpenCubeNormalization
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekBaseChange
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenInterchangeSupplement
import WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenPastingSupplement
import WeilConjectures.AlgebraicGeometry.EtaleRefinementGraphSideTransport
import WeilConjectures.AlgebraicGeometry.EtalePairwiseProductGraphNormalization
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonProperAmbient
import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientFirstSide
import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientData
import WeilConjectures.AlgebraicGeometry.EtaleProperAmbientTransportComposition
import WeilConjectures.AlgebraicGeometry.Derived.DerivedCompactSupportCompositionCoherenceSupplement
import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientSecondSide
import WeilConjectures.AlgebraicGeometry.EtaleGraphProperAmbientMiddle
import WeilConjectures.AlgebraicGeometry.SfExactExchangePasting
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.SixFunctors.LowerShriek.Formalism.BaseChange
import WeilConjectures.AlgebraicGeometry.EtaleGraphComparisonOpenShrink
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkMiddlePasting
import WeilConjectures.AlgebraicGeometry.EtaleGraphNeighborhoodWords
import WeilConjectures.AlgebraicGeometry.EtaleGraphNeighborhoodGeometry
import WeilConjectures.AlgebraicGeometry.EtaleGraphInterchangeData
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkFirstLeg
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkIntersectionWords
import WeilConjectures.AlgebraicGeometry.EtaleGraphShrinkSecondLeg
import WeilConjectures.AlgebraicGeometry.EtaleGraphFromOpenBaseChange
import WeilConjectures.AlgebraicGeometry.Open.OpenSupportRefinementExchange

/-! # Changing the compactifications in an open-support comparison
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

private theorem graphFromOpen_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) (t : EtaleGraphPresentation f) :
    rightDerivedLowerShriekOfCompactificationIso A c d ≪≫
      etaleGraphComparisonFromOpen A d t = etaleGraphComparisonFromOpen A c t := by
  have h := (etaleGraphComparisonBaseChange A c).2.1 d t
  have hn := (etaleGraphComparisonBaseChange A c).2.2.2.2.2.2 c d
  have hc := (etaleGraphComparisonBaseChange A c).2.2.2.1
    (EtaleGraphPresentation.ofCompactification c)
    (EtaleGraphPresentation.ofCompactification d) t
  rw [(etaleGraphComparisonBaseChange A c).2.1 c t, h, hn] at hc
  apply Iso.ext
  have he := congrArg Iso.hom hc
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id_assoc] at he
  apply (cancel_epi (etaleGraphOpenNormalization A c).hom).1
  simpa only [Iso.trans_hom] using he

private theorem graphIso_change
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d e : Compactification f) :
    rightDerivedLowerShriekOfCompactificationIso A c d ≪≫
      openRestrictionGraphIso A d e = openRestrictionGraphIso A c e := by
  have h := congrArg (fun k ↦ k ≪≫ etaleGraphOpenNormalization A e)
    (graphFromOpen_change A c d (EtaleGraphPresentation.ofCompactification e))
  simpa only [openRestrictionGraphIso, etaleGraphComparisonFromOpen,
    EtaleGraphPresentation.ofCompactification, etaleGraphOpenNormalization,
    sfGraphCompactificationComparison, locallyClosedGraphIso,
    locallyClosedGraphSide₁, locallyClosedGraphSide₂, locallyClosedGraphMiddle,
    locallyClosedGraphV, locallyClosedGraphS₁, locallyClosedGraphS₂,
    locallyClosedGraphS₁₂, Iso.trans_assoc] using h

private theorem graphIso_eq_comparison
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (c d : Compactification f) :
    openRestrictionGraphIso A c d = rightDerivedLowerShriekOfCompactificationIso A c d := by
  have h := (etaleGraphComparisonBaseChange A c).2.1 c
    (EtaleGraphPresentation.ofCompactification d)
  rw [(etaleGraphComparisonBaseChange A c).2.2.2.2.2.2 c d] at h
  have he := congrArg (fun k ↦ (etaleGraphOpenNormalization A c).symm ≪≫ k ≪≫
    etaleGraphOpenNormalization A d) h
  simp only [Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_self_id,
    Iso.trans_refl] at he
  change _ = openRestrictionGraphIso A c d at he
  exact he.symm

private theorem graphIso_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    openRestrictionGraphIso A d c =
      asIso (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A)
        r hr) := by
  have h := congrArg (fun k ↦ k ≪≫ etaleGraphOpenNormalization A c)
    (etaleGraphFromOpen_refinement A d c r hr)
  simp only [Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl] at h
  exact h

attribute [local irreducible] openRestrictionGraphIso sfGraphCompactificationComparison
  etaleGraphComparisonFromOpen rightDerivedLowerShriekOfCompactificationIso
  openSupportPullbackIso

private theorem graphIso_comp_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    (b : Compactification f) {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    (openRestrictionGraphIso A b d).hom ≫
        rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A) r hr =
      (openRestrictionGraphIso A b c).hom := by
  have h := graphIso_change A b d c
  rw [← graphIso_eq_comparison, graphIso_refinement A r hr] at h
  exact congrArg Iso.hom h

private theorem support_factor
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} (sq : IsPullback a p f j) (c : Compactification f)
    (b : Compactification p) :
    (openSupportCompactificationIso A sq c b).hom =
      Functor.whiskerRight (openRestrictionGraphIso A b (c.ofIsPullback sq)).hom
        D((j)_!open[ModuleCat.{u + 1} A]) ≫ (openSupportPullbackIso A sq c).hom := by
  simp only [openSupportCompactificationIso, openSupportPullbackIso, Iso.trans_hom,
    Functor.isoWhiskerRight_hom]

private theorem support_refinement
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} [QuasiCompact p] (sq : IsPullback a p f j)
    (b : Compactification p) {c d : Compactification f}
    (r : c.Refinement d) (hr : IsPullback c.i (𝟙 X) r.hom d.i) :
    (openSupportCompactificationIso A sq d b).hom ≫
        Functor.whiskerLeft D((a)_!open[ModuleCat.{u + 1} A])
          (rightDerivedLowerShriekOfCompactificationComparison (ModuleCat.{u + 1} A) r hr) =
      (openSupportCompactificationIso A sq c b).hom := by
  rw [support_factor, support_factor, Category.assoc,
    ← openSupportPullbackIso_refinement A sq r hr, ← Category.assoc,
    ← Functor.whiskerRight_comp, graphIso_comp_refinement]

private theorem support_change_source
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y}
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} [QuasiCompact p] (sq : IsPullback a p f j)
    (c : Compactification f) (b d : Compactification p) :
    Functor.whiskerRight (rightDerivedLowerShriekOfCompactificationIso A b d).hom
        D((j)_!open[ModuleCat.{u + 1} A]) ≫
      (openSupportCompactificationIso A sq c d).hom =
    (openSupportCompactificationIso A sq c b).hom := by
  rw [support_factor, support_factor, ← Category.assoc, ← Functor.whiskerRight_comp]
  rw [← Iso.trans_hom, graphIso_change]

/-- Changing both supplied compactifications commutes with the open-support comparison. -/
theorem openSupportCompactificationIso_naturality
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    {X Y U V : Scheme.{u}} {f : X ⟶ Y} [QuasiCompact f]
    {j : U ⟶ Y} [IsOpenImmersion j] {a : V ⟶ X} [IsOpenImmersion a]
    {p : V ⟶ U} [QuasiCompact p] (sq : IsPullback a p f j)
    (cf df : Compactification f) (cp dp : Compactification p) :
    Functor.whiskerRight (rightDerivedLowerShriekOfCompactificationIso Λ cp dp).hom
        D((j)_!open[ModuleCat.{u + 1} Λ]) ≫
      (openSupportCompactificationIso Λ sq df dp).hom =
    (openSupportCompactificationIso Λ sq cf cp).hom ≫
      Functor.whiskerLeft D((a)_!open[ModuleCat.{u + 1} Λ])
        (rightDerivedLowerShriekOfCompactificationIso Λ cf df).hom := by
  let A := ModuleCat.{u + 1} Λ
  let r := Compactification.inf cf df
  let rc := Compactification.infFst cf df
  let rd := Compactification.infSnd cf df
  let ec : Rf_!(cf)[ModuleCat.{u + 1} Λ] ≅ Rf_!(r)[ModuleCat.{u + 1} Λ] :=
    asIso (rightDerivedLowerShriekOfCompactificationComparison A rc
    (Compactification.isPullback_infFst cf df))
  let ed : Rf_!(df)[ModuleCat.{u + 1} Λ] ≅ Rf_!(r)[ModuleCat.{u + 1} Λ] :=
    asIso (rightDerivedLowerShriekOfCompactificationComparison A rd
    (Compactification.isPullback_infSnd cf df))
  have hc := support_refinement Λ sq cp rc (Compactification.isPullback_infFst cf df)
  have hd := support_refinement Λ sq dp rd (Compactification.isPullback_infSnd cf df)
  have hs := support_change_source Λ sq r cp dp
  change _ ≫ Functor.whiskerLeft D((a)_!open[ModuleCat.{u + 1} Λ]) ec.hom = _ at hc
  change _ ≫ Functor.whiskerLeft D((a)_!open[ModuleCat.{u + 1} Λ]) ed.hom = _ at hd
  conv_rhs => rw [rightDerivedLowerShriekOfCompactificationIso]
  change _ = _ ≫ Functor.whiskerLeft D((a)_!open[A]) (ec.hom ≫ ed.inv)
  rw [Functor.whiskerLeft_comp]
  have hd' : (openSupportCompactificationIso Λ sq df dp).hom =
      (openSupportCompactificationIso Λ sq r dp).hom ≫
        Functor.whiskerLeft D((a)_!open[ModuleCat.{u + 1} Λ]) ed.inv := by
    rw [← hd, Category.assoc, ← Functor.whiskerLeft_comp, Iso.hom_inv_id,
      Functor.whiskerLeft_id', Category.comp_id]
  rw [hd', ← Category.assoc, hs, ← Category.assoc, hc]

end AlgebraicGeometry.Etale
