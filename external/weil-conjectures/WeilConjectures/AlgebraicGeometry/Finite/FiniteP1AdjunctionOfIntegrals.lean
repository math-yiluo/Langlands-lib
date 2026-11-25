/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Compactification.Affine
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.AlgebraicGeometry.FiniteP1ArbitraryBaseIntegrals
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
public import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.AlgebraicGeometry.Scheme
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
public import WeilConjectures.AlgebraicGeometry.DerivedCategories
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.CategoryTheory.AlgebraicInverseImage
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Category.Grp.Limits
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatOnSite
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import Mathlib.CategoryTheory.Limits.ExactFunctor
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.Additive
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.RingedToposFlatPullback
public import WeilConjectures.CategoryTheory.AlgebraicInverseImageOfUniverses
public import Mathlib.CategoryTheory.Types.Basic
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatAlgebraicInverseImageOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatEquationalCriterionOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.FlatLocalRelationsOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.CategoryTheory.Sites.WeakSheafifyAddCommGrpLeftExact
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.LinearAlgebra.TensorProduct.Vanishing
public import Mathlib.RingTheory.TensorProduct.DirectLimitFG
public import Mathlib.LinearAlgebra.TensorProduct.Finiteness
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import WeilConjectures.CategoryTheory.Sites.InverseImageLocalFamilies
public import Mathlib.CategoryTheory.Sites.Sheaf
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import Mathlib.CategoryTheory.Functor.EpiMono
public import Mathlib.CategoryTheory.Limits.Types.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Equalizers
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ScalarTensorComparisonOfUniverses
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.Algebra.Homology.BifunctorMappingCone
public import WeilConjectures.Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Homology.RingedToposAdaptedFlatResolution
public import WeilConjectures.Algebra.Homology.RingedToposPullbackFilteredColimits
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.PreservesSheafification
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.KFlat
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.RingTheory.Flat.CategoryTheory
public import Mathlib.CategoryTheory.ObjectProperty.ColimitsOfShape
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.Algebra.Homology.RingedToposAcyclicKFlatPullback
public import WeilConjectures.Algebra.Homology.BoundedFlatIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.Algebra.Homology.KFlatResolutionIndependentCoefficients
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import WeilConjectures.CategoryTheory.Abelian.Flat.Basic
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.CategoryTheory.Sites.Abelian
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
public import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
public import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
public import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
public import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
public import WeilConjectures.CategoryTheory.IntTensorFamilyIso
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
public import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
public import WeilConjectures.ConstructibleSheaf.Pullback
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
public import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
public import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
public import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.Defs.Filter
public import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
public import WeilConjectures.SixFunctors.Etale.Derived.Tensor
public import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.BaseChange.Square
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1DiagonalComponents
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalMaps
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedCartierKummerSupplement
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.AlgebraicGeometry.ProjectiveLineDiagonalAlphaUnits
public import WeilConjectures.AlgebraicGeometry.FiniteP1DiagonalPicard
public import WeilConjectures.AlgebraicGeometry.P1DiagonalLocalIdeal
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.OfInvertible
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LinearCombination
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Canonical
public import WeilConjectures.AlgebraicGeometry.Modules.ZeroLocus
public import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
public import WeilConjectures.AlgebraicGeometry.Modules.FieldBaseChange
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteChernPullback
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
public import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
public import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
public import WeilConjectures.CategoryTheory.DerivedSingleUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedChernNormalization
public import WeilConjectures.AlgebraicGeometry.SupportedKummerChernRealization
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteConstantUnitComp
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
public import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
public import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.AlgebraicGeometry.FiniteP1KummerNaturality
public import WeilConjectures.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
public import Mathlib.CategoryTheory.Adjunction.Whiskering
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
public import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctBaseChange
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctMate
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
public import WeilConjectures.AlgebraicGeometry.FiniteP1UnitOnPullback
public import WeilConjectures.AlgebraicGeometry.FiniteP1KummerSplitting
public import WeilConjectures.AlgebraicGeometry.FiniteP1NoetherianBase
public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Submodule
public import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeModN
public import WeilConjectures.AlgebraicGeometry.TorsionAssembly
public import WeilConjectures.SixFunctors.BaseChange.Derived
public import WeilConjectures.AlgebraicGeometry.TorsionEtaleSheaf
public import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
public import WeilConjectures.SixFunctors.BaseChange.DerivedForget
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.AbTorsionSheaf
public import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.ProjectiveLine
public import WeilConjectures.SixFunctors.Etale.Derived.DirectImageVanishingTorsion
public import WeilConjectures.SixFunctors.BaseChange.DerivedUnboundedFac
public import WeilConjectures.AlgebraicGeometry.ProperUnboundedBaseChangeForgetful
public import Mathlib.Data.ZMod.Basic
public import WeilConjectures.AlgebraicGeometry.UnboundedCoefficientForgetfulAux
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.DerivedBaseChange
public import WeilConjectures.AlgebraicGeometry.UnboundedAbelianExchangeComparison
public import WeilConjectures.AlgebraicGeometry.ChosenCartesianSquare
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianDerivedDirectImageComparison
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianKInjectiveDirectImageAcyclic
public import WeilConjectures.AlgebraicGeometry.EtaleModuleAbelianRingedPresentation
public import WeilConjectures.CategoryTheory.Ringed.RingedToposMorphismSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.CartesianMonoidal
public import WeilConjectures.AlgebraicGeometry.ModuleSheafConstantRingEquivalence
public import WeilConjectures.CategoryTheory.ContinuousRingedToposModuleDirectImage
public import WeilConjectures.CategoryTheory.GeometricModuleConstruction
public import WeilConjectures.CategoryTheory.RingedToposRingData
public import WeilConjectures.CategoryTheory.AdjunctionRingOperations
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.CategoryTheory.Adjunction.Basic
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Mod
public import WeilConjectures.CategoryTheory.ProperBaseChange.RestrictionRingedToposModuleDirectImageSupplement
public import WeilConjectures.CategoryTheory.RingedToposDerivedPushforwardComposition
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import WeilConjectures.CategoryTheory.RingedSiteKInjectiveResolutions
public import WeilConjectures.Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.CategoryTheory.Localization.DerivabilityStructure.Derives
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Defs
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.KInjectiveResolution
public import Mathlib.Algebra.Homology.DerivedCategory.Fractions
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.CategoryTheory.GeometricModuleTransport
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import WeilConjectures.CategoryTheory.GeometricRingTransport
public import WeilConjectures.CategoryTheory.SheavesAlgebraicStructuresRingCore
public import WeilConjectures.CategoryTheory.SheafRingObjectReconstruction
public import WeilConjectures.CategoryTheory.Adjunction.FiniteProductRingFunctor
public import WeilConjectures.Algebra.Homology.Module.ModulePullbackPushforwardAdjunctionSupplement
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Comp
public import WeilConjectures.AlgebraicGeometry.ModuleAbelianUnderivedExchange
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import WeilConjectures.AlgebraicGeometry.FiniteP1DiagonalChernComponents
public import WeilConjectures.AlgebraicGeometry.RelativeEffectiveCartier
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
public import WeilConjectures.AlgebraicGeometry.FiniteP1DiagonalAlpha
public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import WeilConjectures.AlgebraicGeometry.Finite.FiniteP1CoordinateKernel
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-! # Assembling the finite projective-line diagonal kernel

Source: blueprint latest, sec-six-functors-basics/sk-prop-geo-p1-adjunction/
`thm-amb-p1-adjunction.proof.md`, unit construction and both triangles.
(blueprint: lem-sp-finite-p1-adjunction-of-integrals).
-/

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option Elab.async false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

attribute [local irreducible] rightDerivedLowerShriek
  SfDiagonalKernel.unit SfDiagonalKernel.counit

/-- The left triangle identity of a candidate unit and counit, componentwise, as in the field
`Adjunction.left_triangle_components`. -/
def _root_.CategoryTheory.Adjunction.LeftTriangleComponents {C D : Type*} [Category C]
    [Category D] (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ⟶ F ⋙ G) (ε : G ⋙ F ⟶ 𝟭 D) : Prop :=
  ∀ X : C, F.map (η.app X) ≫ ε.app (F.obj X) = 𝟙 (F.obj X)

/-- The right triangle identity of a candidate unit and counit, componentwise, as in the field
`Adjunction.right_triangle_components`. -/
def _root_.CategoryTheory.Adjunction.RightTriangleComponents {C D : Type*} [Category C]
    [Category D] (F : C ⥤ D) (G : D ⥤ C) (η : 𝟭 C ⟶ F ⋙ G) (ε : G ⋙ F ⟶ 𝟭 D) : Prop :=
  ∀ Y : D, η.app (G.obj Y) ≫ G.map (ε.app Y) = 𝟙 (G.obj Y)

/-- The adjunction with given unit and counit satisfying both componentwise triangle
identities. -/
@[simps]
def _root_.CategoryTheory.Adjunction.ofTriangleComponents {C D : Type*} [Category C]
    [Category D] {F : C ⥤ D} {G : D ⥤ C} (η : 𝟭 C ⟶ F ⋙ G) (ε : G ⋙ F ⟶ 𝟭 D)
    (hl : Adjunction.LeftTriangleComponents F G η ε)
    (hr : Adjunction.RightTriangleComponents F G η ε) : F ⊣ G where
  unit := η
  counit := ε
  left_triangle_components := hl
  right_triangle_components := hr

namespace SfDiagonalKernel

/-- The first triangle identity of the diagonal-kernel unit and counit, in the form of the
corresponding field of `Adjunction`. -/
theorem left_triangle_components
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsProper f]
    {B : DerivedCategoryModule A X} (k : TraceDiagonalDatum A f B)
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hJ : Scheme.IsLisseRankOneSheaf J) (n : ℤ)
    (e : B ≅ (CoordinateTrace.pull A f).obj (CoordinateTrace.shiftedLine A J n))
    (h : Integrals A k (CoordinateTrace.shiftedLine A J n) e) :
    Adjunction.LeftTriangleComponents (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
      (CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B)
      (unit A k) (counit A k) :=
  (triangles A k J hJ n e h).1

/-- The second triangle identity of the diagonal-kernel unit and counit, in the form of the
corresponding field of `Adjunction`. -/
theorem right_triangle_components
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsProper f]
    {B : DerivedCategoryModule A X} (k : TraceDiagonalDatum A f B)
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hJ : Scheme.IsLisseRankOneSheaf J) (n : ℤ)
    (e : B ≅ (CoordinateTrace.pull A f).obj (CoordinateTrace.shiftedLine A J n))
    (h : Integrals A k (CoordinateTrace.shiftedLine A J n) e) :
    Adjunction.RightTriangleComponents (rightDerivedLowerShriek (ModuleCat.{u + 1} A) f)
      (CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B)
      (unit A k) (counit A k) :=
  (triangles A k J hJ n e h).2

/-- The adjunction `Rf_! ⊣ f^*(-) ⊗ᴸ B` of a trace-diagonal kernel whose two diagonal
integrals are identities, for `B` the pullback of an even-shifted lisse rank-one line: its unit is
`SfDiagonalKernel.unit` and its counit is `SfDiagonalKernel.counit`, the inverse projection map
followed by the trace and the left unitor. The functors are kept abstract.

Source: blueprint latest, thm-amb-p1-adjunction.proof.md, the unit construction and both
triangles (blueprint: lem-sp-finite-p1-adjunction-of-integrals). -/
noncomputable def adjunction
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsProper f]
    {B : DerivedCategoryModule A X} (k : TraceDiagonalDatum A f B)
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hJ : Scheme.IsLisseRankOneSheaf J) (n : ℤ)
    (e : B ≅ (CoordinateTrace.pull A f).obj (CoordinateTrace.shiftedLine A J n))
    (h : Integrals A k (CoordinateTrace.shiftedLine A J n) e) :
    rightDerivedLowerShriek (ModuleCat.{u + 1} A) f ⊣
      CoordinateTrace.pull A f ⋙ (derivedTensor (ModuleCat.{u + 1} A) X).obj B :=
  Adjunction.ofTriangleComponents (unit A k) (counit A k)
    (left_triangle_components A k J hJ n e h) (right_triangle_components A k J hJ n e h)

@[simp]
theorem adjunction_unit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsProper f]
    {B : DerivedCategoryModule A X} (k : TraceDiagonalDatum A f B)
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hJ : Scheme.IsLisseRankOneSheaf J) (n : ℤ)
    (e : B ≅ (CoordinateTrace.pull A f).obj (CoordinateTrace.shiftedLine A J n))
    (h : Integrals A k (CoordinateTrace.shiftedLine A J n) e) :
    (adjunction A k J hJ n e h).unit = unit A k :=
  rfl

@[simp]
theorem adjunction_counit
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} {f : X ⟶ Y} [IsProper f]
    {B : DerivedCategoryModule A X} (k : TraceDiagonalDatum A f B)
    (J : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))
    (hJ : Scheme.IsLisseRankOneSheaf J) (n : ℤ)
    (e : B ≅ (CoordinateTrace.pull A f).obj (CoordinateTrace.shiftedLine A J n))
    (h : Integrals A k (CoordinateTrace.shiftedLine A J n) e) :
    (adjunction A k J hJ n e h).counit = counit A k :=
  rfl

end SfDiagonalKernel

/-- The finite Tate line `Λ_S(1)` is lisse of rank one when the positive integer `N`, which
annihilates `Λ`, is invertible on `S`. -/
theorem isLisseRankOneSheaf_finiteEtaleTateLine
    (Λ : Type (u + 1)) [CommRing Λ]
    (N : ℕ) (hN : 0 < N) (hΛ : (N : Λ) = 0)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤))) :
    Scheme.IsLisseRankOneSheaf (Scheme.finiteEtaleTateLine S N Λ hΛ) := by
  have hInv (s : S) : IsUnit (N : S.presheaf.stalk s) := by
    simpa only [map_natCast] using hS.map (S.presheaf.germ ⊤ s (by trivial)).hom
  obtain ⟨U, hU⟩ := Scheme.finiteEtaleTateLine_localTrivial S N hN hInv Λ hΛ
  exact ⟨U, hU⟩

/-- The projective-line adjunction assembled from a supplied base-compatible finite-root
splitting and a supported diagonal class `κ` whose two diagonal integrals are identities: the
kernel adjunction `SfDiagonalKernel.adjunction` of `finiteP1CoordinateKernel`, read through
`Rq_! ≅ Rq_*`, with the shift moved outside the right tensor factor.

Source: blueprint `thm-amb-p1-adjunction.proof.md`, the displayed unit and both
triangle computations, using the arbitrary-base integrals of
`sk-prop-sp-tower-geometric-p1.proof.md`.
(blueprint: lem-sp-finite-p1-adjunction-of-integrals).

Proof in words: write q for the projective-line projection. Reindex the standard
ULift (Fin 2) homogeneous coordinates by Option (ULift (Fin 1)); the induced
scheme isomorphism commutes with q. Transport the splitting, its trace, and the
supported diagonal class through that isomorphism. Both diagonal integrals
remain identities, by functoriality and cancellation of the comparison inverses.
The counit is inverse proper projection, then tensor with the supplied trace,
then the tensor-unit constraint. To construct the unit on any complex M, identify
M with Rp2_*Delta_*M using p2 Delta = id. The closed-immersion projection formula
identifies Delta_*M with Delta_*Lambda tensor p1^*M. Tensor the supported diagonal
class with p1^*M, push along p2, and apply inverse proper exchange to obtain
q^*Rq_*M tensor Lambda(1)[2]. These operations give natural transformations.
For the first triangle, proper exchange, direct-image composition and projection
naturality rewrite the composite as Rq_* of M tensored with the first diagonal
integral. The first integral identity makes it the identity. In the second
triangle the common coefficient p1^*q^*K = p2^*q^*K comes outside p2_* by proper
projection; the remaining kernel map is the second diagonal integral, hence the
identity. The trace base-change equation supplied by hbc identifies the traces
in these two computations with the chosen splitting traces. The shifted line
has even shift two, so moving its two copies past each other gives sign +1.
The two triangles produce the adjunction on all unbounded complexes. Finally
move the shift outside right tensor using derivedTensorRightShiftIso. No
normalized abstract twist, normalization comparison, or new splitting is used. -/
noncomputable def finiteP1AdjunctionOfIntegrals
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (N : ℕ) (hN : 0 < N) (hΛ : (N : Λ) = 0)
    (t : OrdinaryFiniteTwistTransport Λ N hΛ)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting Λ N hΛ t T hT)
    (hbc : ArbitraryBaseFiniteP1BaseChange Λ N hΛ t d)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (κ : Abelian.Ext
      (C := Sheaf
        (Limits.pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ))
      ((lowerStar (ModuleCat.{u + 1} Λ)
        (Z := ProjectiveLine S)
        (Y := Limits.pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
        (Limits.pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteConstant Λ (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (Limits.pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N Λ hΛ) 2)
    (hκ : ∀ a : Bool, ordinaryFiniteP1DiagonalSupportedMap Λ N hΛ S a κ ≫
        arbitraryBaseFiniteP1DiagonalTrace Λ N hΛ t d S hS a =
      𝟙 (ordinaryFiniteUnit Λ (ProjectiveLine S))) :
    R((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)_*[ModuleCat.{u + 1} Λ]) ⊣
      L((ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S)^*[ModuleCat.{u + 1} Λ]) ⋙
        ((derivedTensor (ModuleCat.{u + 1} Λ)
          ℙ(Option (ULift.{u} (Fin 1)); S)).flip.obj
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateLine ℙ(Option (ULift.{u} (Fin 1)); S) N Λ hΛ)) ⋙
          shiftFunctor _ (2 : ℤ)) :=
  ((SfDiagonalKernel.adjunction Λ (finiteP1CoordinateKernel Λ N hΛ t d hbc S hS κ)
      (Scheme.finiteEtaleTateLine S N Λ hΛ)
      (isLisseRankOneSheaf_finiteEtaleTateLine Λ N hN hΛ S hS) 1
      (finiteP1CoordinateKernelIso Λ N hΛ t S hS)
      (finiteP1CoordinateKernel_integrals Λ N hΛ t d hbc S hS κ hκ)).ofNatIsoLeft
    (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ)
      (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))).ofNatIsoRight
    (Functor.isoWhiskerLeft _
      ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) ℙ(Option (ULift.{u} (Fin 1)); S)).app
          (((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateLine ℙ(Option (ULift.{u} (Fin 1)); S) N Λ
              hΛ))⟦(2 : ℤ)⟧) ≪≫
        derivedTensorRightShiftIso (ModuleCat.{u + 1} Λ)
          ((_root_.DerivedCategory.singleFunctor _ 0).obj
            (Scheme.finiteEtaleTateLine ℙ(Option (ULift.{u} (Fin 1)); S) N Λ hΛ)) (2 : ℤ)))

/-- `finiteP1AdjunctionOfIntegrals` is the kernel adjunction `SfDiagonalKernel.adjunction` of
`finiteP1CoordinateKernel` transported along `Rq_! ≅ Rq_*` and the rearrangement of the shifted
tensor factor; its unit and counit follow from `SfDiagonalKernel.adjunction_unit`,
`SfDiagonalKernel.adjunction_counit` and the `Adjunction.ofNatIsoLeft`/`ofNatIsoRight` lemmas. -/
theorem finiteP1AdjunctionOfIntegrals_eq
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]
    (N : ℕ) (hN : 0 < N) (hΛ : (N : Λ) = 0)
    (t : OrdinaryFiniteTwistTransport Λ N hΛ)
    (d : ∀ (T : Scheme.{u}) (hT : IsUnit (N : Γ(T, ⊤))),
      ArbitraryBaseFiniteP1Splitting Λ N hΛ t T hT)
    (hbc : ArbitraryBaseFiniteP1BaseChange Λ N hΛ t d)
    (S : Scheme.{u}) (hS : IsUnit (N : Γ(S, ⊤)))
    (κ : Abelian.Ext
      (C := Sheaf
        (Limits.pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)).smallEtaleTopology
        (ModuleCat.{u + 1} Λ))
      ((lowerStar (ModuleCat.{u + 1} Λ)
        (Z := ProjectiveLine S)
        (Y := Limits.pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S))
        (Limits.pullback.diagonal (ProjectiveLine S ↘ S))).obj
        (ordinaryFiniteConstant Λ (ProjectiveLine S)))
      (Scheme.finiteEtaleTateLine
        (Limits.pullback (ProjectiveLine S ↘ S) (ProjectiveLine S ↘ S)) N Λ hΛ) 2)
    (hκ : ∀ a : Bool, ordinaryFiniteP1DiagonalSupportedMap Λ N hΛ S a κ ≫
        arbitraryBaseFiniteP1DiagonalTrace Λ N hΛ t d S hS a =
      𝟙 (ordinaryFiniteUnit Λ (ProjectiveLine S))) :
    finiteP1AdjunctionOfIntegrals Λ N hN hΛ t d hbc S hS κ hκ =
    ((SfDiagonalKernel.adjunction Λ (finiteP1CoordinateKernel Λ N hΛ t d hbc S hS κ)
        (Scheme.finiteEtaleTateLine S N Λ hΛ)
        (isLisseRankOneSheaf_finiteEtaleTateLine Λ N hN hΛ S hS) 1
        (finiteP1CoordinateKernelIso Λ N hΛ t S hS)
        (finiteP1CoordinateKernel_integrals Λ N hΛ t d hbc S hS κ hκ)).ofNatIsoLeft
      (rightDerivedLowerShriekIsoRightDerivedLowerStar (ModuleCat.{u + 1} Λ)
        (ℙ(Option (ULift.{u} (Fin 1)); S) ↘ S))).ofNatIsoRight
      (Functor.isoWhiskerLeft _
        ((derivedTensorSymmetry (ModuleCat.{u + 1} Λ) ℙ(Option (ULift.{u} (Fin 1)); S)).app
            (((_root_.DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateLine ℙ(Option (ULift.{u} (Fin 1)); S) N Λ
                hΛ))⟦(2 : ℤ)⟧) ≪≫
          derivedTensorRightShiftIso (ModuleCat.{u + 1} Λ)
            ((_root_.DerivedCategory.singleFunctor _ 0).obj
              (Scheme.finiteEtaleTateLine ℙ(Option (ULift.{u} (Fin 1)); S) N Λ hΛ)) (2 : ℤ))) :=
  rfl

end AlgebraicGeometry.Etale
