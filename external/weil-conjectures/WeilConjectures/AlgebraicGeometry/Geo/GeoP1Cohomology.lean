/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.AlgebraicGeometry.Sites.Proetale
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
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1Decomposition
public import WeilConjectures.AlgebraicGeometry.Projective.ProjectiveLineTraceSupplement
public import WeilConjectures.AlgebraicGeometry.Geo.GeoCartierCycleClass
public import WeilConjectures.AlgebraicGeometry.Comparison.ComparisonDerivedPullbackFixed
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Tensor
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.Derived.Comparison
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Twist

import all WeilConjectures.AlgebraicGeometry.Projection.ProjectionComparisonEtaleOrigin
import WeilConjectures.AlgebraicGeometry.Sp.SpDirectImageEtaleMate
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedEtaleCompactSupportComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1Untwist
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DatumUniqueness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1KummerMaps
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Data
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import Mathlib.AlgebraicGeometry.Sites.Etale
import Mathlib.AlgebraicGeometry.Scheme
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
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
import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import WeilConjectures.CategoryTheory.AlgebraicInverseImage
import Mathlib.Algebra.Category.ModuleCat.Sheaf
import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.CategoryTheory.Sites.Whiskering
import Mathlib.CategoryTheory.Sites.Equivalence
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.Algebra.Homology.BifunctorShift
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import Mathlib.CategoryTheory.Limits.EssentiallySmall
import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Adjunction.Limits
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
import Mathlib.CategoryTheory.Sites.EpiMono
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.CategoryTheory.Sites.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import WeilConjectures.ConstructibleSheaf.Defs
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import WeilConjectures.CategoryTheory.IntTensorFamilyIso
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import Mathlib.CategoryTheory.Abelian.Refinements
import Mathlib.Algebra.Homology.ShortComplex.Exact
import WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.Topology.Defs.Filter
import WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import WeilConjectures.SixFunctors.Etale.Derived.Tensor
import WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.BaseChange.Square
import WeilConjectures.SixFunctors.Etale.Derived.Shift
import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1ExchangeIso
import WeilConjectures.SixFunctors.Etale.BaseChangeTheorems.Proper
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteAdjunctScalarFaithfulness
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassScalarFaithfulness
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Linear
import WeilConjectures.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctBaseChange
import WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
import WeilConjectures.CategoryTheory.DerivedSingleUnit
import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctMate
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerAffineLine
import WeilConjectures.AlgebraicGeometry.ProjectiveLineGenusZero
import WeilConjectures.AlgebraicGeometry.Curve
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace
import WeilConjectures.Topology.RingedSpaceModuleCohomology
import WeilConjectures.AlgebraicGeometry.Cohomology.ProjectiveLine
import WeilConjectures.AlgebraicGeometry.ModuleCohomologySourceComparison
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.LineSmooth
import WeilConjectures.AlgebraicGeometry.ProjectiveSpace.Line
import WeilConjectures.Algebra.Homology.DerivedCategory.SingleHomology
import WeilConjectures.AlgebraicGeometry.Curve.RootsOfUnityTop
import WeilConjectures.AlgebraicGeometry.Curve.Estimate
import WeilConjectures.AlgebraicGeometry.ProjectiveLineTateCoefficientGenerator
import WeilConjectures.AlgebraicGeometry.ProjectiveLineConstantCoefficientGenerator
import WeilConjectures.AlgebraicGeometry.Curve.AffineLineKummer
import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClassGenerator
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteGeometricPointHomology
import WeilConjectures.SixFunctors.Etale.Derived.AlgClosedField
import WeilConjectures.SixFunctors.Etale.Derived.Kunneth.KunnethMap
import WeilConjectures.CategoryTheory.DerivedCategory.HomSingleProjective
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFibreHomologyComparison
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1FibreHomologyCard
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassComparison

/-!
# The ordinary pro-etale projective-line decomposition and trace

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-geo-p1-cohomology,
(G2), (G3) and proof steps 1--9; Stacks Project, Tag 0GL5
(blueprint: lemma-cohomology-projective-line-trace).

The coefficient object and signed twists are comparison pullbacks of the existing
ordinary etale objects. This is the ordinary small pro-etale derived category.
The comparison map is the counit mate, and the two decomposition maps use the
same Kummer-normalized Chern class. All helpers spell out these canonical arrows.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.unusedSimpArgs false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.ProEtale

attribute [local irreducible] Etale.projectiveLineTraceDatum Etale.projectiveLineTraceTransport
  BoundaryComparison.directImageMate
attribute [local irreducible] Etale.ordinaryFiniteTensor Scheme.rootsOfUnitySheaf
  ProjectiveSpace.twist Etale.ordinaryFiniteP1ChernSpec Etale.ordinaryFiniteP1Exchange
  Etale.ordinaryFiniteP1DecompositionSourceMap Etale.ordinaryFiniteShiftedLinePullback
  Etale.ordinaryFiniteP1Unit Etale.ordinaryFiniteP1ChernPushforward
  Etale.p1DecompositionMap Etale.p1DecompositionChernAdjoint

/-- Exact comparison on the entire ordinary derived category; its bounded-below
restriction is `siteComparisonDerivedPullbackPlus`.
Source: blueprint (G2), proof step 6 (blueprint: lemma-cohomology-projective-line-trace). -/
abbrev geoP1Comparison (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :=
  (comparisonUpperStar (ModuleCat.{u + 1} A) S).mapDerivedCategory

/-- The existing exact inverse image, expressed as its left derived functor.
Source: blueprint (G2), base-change clause (blueprint: lemma-cohomology-projective-line-trace). -/
@[implicit_reducible]
def geoP1Pullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (upperStar (ModuleCat.{u + 1} A) f).leftDerivedFunctor

/-- The existing K-injective derived direct image on ordinary module sheaves.
Source: blueprint (G2) (blueprint: lemma-cohomology-projective-line-trace). -/
@[implicit_reducible]
def geoP1Pushforward (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :=
  (lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor

/-- Pullback commutes with comparison by the actual site-comparison square.
Source: blueprint proof step 7 (blueprint: lemma-cohomology-projective-line-trace). -/
def geoP1PullComparison (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    geoP1Comparison A Y ⋙ geoP1Pullback A f ≅
      Etale.ordinaryFinitePullback A f ⋙ geoP1Comparison A X :=
  Functor.isoWhiskerLeft _ (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) ≪≫
    Functor.mapDerivedCategoryCompIso _ _ ≪≫
    Functor.mapDerivedCategoryNatIso
      (comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f) ≪≫
    (Functor.mapDerivedCategoryCompIso _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f).symm _

/-- The canonical unbounded comparison mate. Only its bounded-below instances
are asserted invertible below. Its adjunct is the pull comparison followed by the
image of the etale counit; no arbitrary pushforward comparison is selected.
Source: blueprint proof steps 6--7 (blueprint: lemma-cohomology-projective-line-trace). -/
def geoP1PushComparison (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : Etale.DerivedCategoryModule A X) :
    (geoP1Comparison A Y).obj ((Etale.ordinaryFinitePushforward A f).obj K) ⟶
      (geoP1Pushforward A f).obj ((geoP1Comparison A X).obj K) :=
  (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).homEquiv _ _
    ((geoP1PullComparison A f).hom.app _ ≫
      (geoP1Comparison A X).map
        ((Etale.derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) f).counit.app K))

attribute [local irreducible] geoP1PushComparison

/-- Comparison preserves the specified ordered sum by its two injections.
Source: blueprint proof step 6 (blueprint: lemma-cohomology-projective-line-trace). -/
def geoP1SumComparison (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    (K L : Etale.DerivedCategoryModule A S) :
    ((geoP1Comparison A S).obj K ⊞ (geoP1Comparison A S).obj L) ⟶
      (geoP1Comparison A S).obj (K ⊞ L) :=
  biprod.desc ((geoP1Comparison A S).map biprod.inl)
    ((geoP1Comparison A S).map biprod.inr)

/-- The constant coefficient object, canonically the constant pro-etale sheaf
in degree zero by the exact comparison constant-sheaf identification.
Source: blueprint (G2) (blueprint: lemma-cohomology-projective-line-trace). -/
abbrev geoP1Unit (A : Type (u + 1)) [CommRing A] (S : Scheme.{u}) :=
  (geoP1Comparison A S).obj (Etale.ordinaryFiniteUnit A S)

/-- The signed finite Tate object, pulled through comparison and shifted.
Exact comparison commutes with shifts, so this is Λ_S(a)[b].
Source: blueprint definition of the twists (blueprint: lemma-cohomology-projective-line-trace). -/
abbrev geoP1Twist (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u}) (a b : ℤ) :=
  (geoP1Comparison A S).obj (Etale.p1DecompositionTwist A N hA S a b)

/-- The same normalized Kummer Chern arrow used by the ordinary trace. Its
specification is the scalar Kummer boundary of the existing projective-space O(1),
not an arbitrary degree-two class. Its comparison image is the pro-etale class.
Source: blueprint proof steps 1, 2, 6 (blueprint: lemma-cohomology-projective-line-trace). -/
abbrev geoP1EtaleChern (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :=
  (Etale.projectiveLineTraceDatum N hN A hA S hS).chern

/-- The specified map (G2), obtained from the unit and the adjoint of the
Kummer Chern class, then the canonical direct-image comparison mate.
Source: blueprint (G2), proof steps 5--6 (blueprint: lemma-cohomology-projective-line-trace). -/
def geoP1DecompositionMap (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    (geoP1Unit A S ⊞ geoP1Twist A N hA S (-1) (-2)) ⟶
      (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj (geoP1Unit A (ProjectiveLine S)) :=
  geoP1SumComparison A S _ _ ≫
    (geoP1Comparison A S).map
      (Etale.p1DecompositionMap A N hN hA S hS (geoP1EtaleChern A N hN hA S hS)) ≫
    geoP1PushComparison A (ProjectiveLine S ↘ S) _

/-- The twist of (G2) by (1)[2], expressed in the order Λ(1)[2] plus Λ.
Its two components are the shifted twisted unit and the very same Chern adjunct.
The projection formula and evaluation identify this with twisting (G2).
Source: blueprint proof step 8 (blueprint: lemma-cohomology-projective-line-trace). -/
def geoP1TwistedMap (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    (geoP1Twist A N hA S 1 2 ⊞ geoP1Unit A S) ⟶
      (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
        (geoP1Twist A N hA (ProjectiveLine S) 1 2) :=
  geoP1SumComparison A S _ _ ≫
    (geoP1Comparison A S).map
      (Etale.projectiveLineTraceDatum N hN A hA S hS).decomposition.hom ≫
    geoP1PushComparison A (ProjectiveLine S ↘ S)
      ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)

/-- The normalized constant-object pullback through the comparison square.
Source: blueprint base-change clause (blueprint: lemma-cohomology-projective-line-trace). -/
def geoP1UnitPullback (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (geoP1Pullback A f).obj (geoP1Unit A Y) ≅ geoP1Unit A X :=
  (geoP1PullComparison A f).app _ ≪≫
    (geoP1Comparison A X).mapIso (Etale.ordinaryFiniteUnitPullback A f)

/-- The roots-normalized signed-twist pullback, with the exact comparison square.
Source: blueprint base-change clause (blueprint: lemma-cohomology-projective-line-trace). -/
def geoP1TwistPullback (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) (a b : ℤ) :
    (geoP1Pullback A f).obj (geoP1Twist A N hA Y a b) ≅ geoP1Twist A N hA X a b :=
  (geoP1PullComparison A f).app _ ≪≫
    (geoP1Comparison A X).mapIso (Etale.p1DecompositionTwistPullback A N hN hA f hY a b)

/-- Canonical comparison on the ordered summands of (G2).
Source: blueprint proof step 7 (blueprint: lemma-cohomology-projective-line-trace). -/
def geoP1SourceMap (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S' S : Scheme.{u}} (g : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) :
    (geoP1Pullback A g).obj (geoP1Unit A S ⊞ geoP1Twist A N hA S (-1) (-2)) ⟶
      (geoP1Unit A S' ⊞ geoP1Twist A N hA S' (-1) (-2)) :=
  biprod.lift
    ((geoP1Pullback A g).map biprod.fst ≫ (geoP1UnitPullback A g).hom)
    ((geoP1Pullback A g).map biprod.snd ≫
      (geoP1TwistPullback A N hN hA g hS (-1) (-2)).hom)

/-- The actual derived exchange map of the Cartesian projective-line square.
This is the mate specified by the recorded derived adjunction, for every base map.
Source: blueprint proof step 7 (blueprint: lemma-cohomology-projective-line-trace). -/
def geoP1Exchange (A : Type (u + 1)) [CommRing A]
    {S' S : Scheme.{u}} (g : S' ⟶ S)
    (K : DerivedCategory (Sheaf (Scheme.ProEt.topology (ProjectiveLine S))
      (ModuleCat.{u + 1} A))) :
    (geoP1Pullback A g).obj ((geoP1Pushforward A (ProjectiveLine S ↘ S)).obj K) ⟶
      (geoP1Pushforward A (ProjectiveLine S' ↘ S')).obj
        ((geoP1Pullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).obj K) :=
  (derivedBaseChangeMap (ModuleCat.{u + 1} A)
    (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq).app K

/-- Exchange on the coefficient object with its canonical constant identification.
Source: blueprint (G2), base-change clause (blueprint: lemma-cohomology-projective-line-trace). -/
def geoP1UnitExchange (A : Type (u + 1)) [CommRing A]
    {S' S : Scheme.{u}} (g : S' ⟶ S) :
    (geoP1Pullback A g).obj
        ((geoP1Pushforward A (ProjectiveLine S ↘ S)).obj (geoP1Unit A (ProjectiveLine S))) ⟶
      (geoP1Pushforward A (ProjectiveLine S' ↘ S')).obj (geoP1Unit A (ProjectiveLine S')) :=
  geoP1Exchange A g _ ≫ (geoP1Pushforward A (ProjectiveLine S' ↘ S')).map
    (geoP1UnitPullback A
      (X := ProjectiveLine S') (Y := ProjectiveLine S)
      (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom

/-- Exchange on the shifted positive twist, using the normalized finite-line pullback.
Source: blueprint proof steps 8--9 (blueprint: lemma-cohomology-projective-line-trace). -/
def geoP1TwistExchange (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S' S : Scheme.{u}} (g : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) :
    (geoP1Pullback A g).obj ((geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
      (geoP1Twist A N hA (ProjectiveLine S) 1 2)) ⟶
      (geoP1Pushforward A (ProjectiveLine S' ↘ S')).obj
        (geoP1Twist A N hA (ProjectiveLine S') 1 2) :=
  geoP1Exchange A g _ ≫ (geoP1Pushforward A (ProjectiveLine S' ↘ S')).map
    (geoP1TwistPullback A N hN hA
      (X := ProjectiveLine S') (Y := ProjectiveLine S) (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)
      ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
        hS.map (ProjectiveLine S ↘ S).appTop.hom) 1 2).hom

/-- The normalized trace is projection onto the constant second summand after the
inverse of the twisted (G2). The isomorphism's hom is fixed in the theorem below.
Source: blueprint (G3) (blueprint: lemma-cohomology-projective-line-trace). -/
def geoP1Trace (A : Type (u + 1)) [CommRing A] (N : ℕ) (hA : (N : A) = 0)
    (S : Scheme.{u})
    (b : (geoP1Twist A N hA S 1 2 ⊞ geoP1Unit A S) ≅
      (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
        (geoP1Twist A N hA (ProjectiveLine S) 1 2)) :
    (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
      (geoP1Twist A N hA (ProjectiveLine S) 1 2) ⟶ geoP1Unit A S :=
  b.inv ≫ biprod.snd

@[irreducible]
private def normalizedTransport (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0) :
    Etale.OrdinaryFiniteTwistTransport A N hA where
  roots := (Etale.p1DecompositionTwistTransport A N hN hA).roots
  line := fun f hY ↦ (Etale.p1DecompositionTwistTransport A N hN hA).line
    f hY ((map_natCast f.appTop.hom N) ▸ hY.map f.appTop.hom) 1
  roots_normalization := (Etale.p1DecompositionTwistTransport A N hN hA).roots_normalization
  line_normalization := fun f hY ↦
    (Etale.p1DecompositionTwistTransport A N hN hA).line_normalization f hY _

private theorem linePullback_eq (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    t.line f hY = Etale.p1DecompositionSheafPullback A N hN hA f hY 1 := by
  have ht := congrArg (fun t : Etale.OrdinaryFiniteTwistTransport A N hA ↦ t.line f hY)
    (Etale.ordinaryFiniteTwistTransport_unique A N hA t (normalizedTransport A N hN hA))
  simpa only [normalizedTransport, Etale.p1DecompositionSheafPullback] using ht

/-- `shiftedSinglePullbackIsoWith` is `p1DecompositionShiftedComparison` for the derived inverse
image. -/
private theorem shiftedSinglePullbackIsoWith_eq {B : Type*} [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (sY : Sheaf Y.smallEtaleTopology B ⥤ DerivedCategory (Sheaf Y.smallEtaleTopology B))
    (sX : Sheaf X.smallEtaleTopology B ⥤ DerivedCategory (Sheaf X.smallEtaleTopology B))
    (c : sY ⋙ (Etale.upperStar B f).leftDerivedFunctor ≅ Etale.upperStar B f ⋙ sX)
    (J : Sheaf Y.smallEtaleTopology B) (J' : Sheaf X.smallEtaleTopology B)
    (e : (Etale.upperStar B f).obj J ≅ J') (n : ℤ) :
    Etale.shiftedSinglePullbackIsoWith B f sY sX c J J' e n =
      letI := Etale.commShiftLeftDerivedUpperStar B f
      Etale.p1DecompositionShiftedComparison (Etale.upperStar B f).leftDerivedFunctor sY sX
        (Etale.upperStar B f) c J J' e n := by
  unfold Etale.p1DecompositionShiftedComparison Etale.shiftedSinglePullbackIsoWith
  rfl

/-- Congruence for a whiskered composite of isomorphisms. -/
private theorem whiskerLeft_trans_heq {C D E : Type*} [Category C] [Category D] [Category E]
    (s s' : C ⥤ D) (hs : s = s') (G H G' H' : D ⥤ E) (hG : G = G') (hH : H = H')
    (α : G ≅ H) (α' : G' ≅ H') (hα : HEq α α')
    (K K' : C ⥤ E) (hK : K = K') (β : s ⋙ H ≅ K) (β' : s' ⋙ H' ≅ K') (hβ : HEq β β') :
    HEq (Functor.isoWhiskerLeft s α ≪≫ β) (Functor.isoWhiskerLeft s' α' ≪≫ β') := by
  subst hs hG hH hK
  cases hα
  cases hβ
  rfl

/-- Congruence for `p1DecompositionShiftedComparison`, with every argument replaced. -/
private theorem shiftedComparison_heq {C D C₀ D₀ : Type*}
    [Category C] [Category D] [Category C₀] [Category D₀]
    [HasShift C ℤ] [HasShift D ℤ]
    (F F' : C ⥤ D) (hF : F = F') [iF : F.CommShift ℤ] [iF' : F'.CommShift ℤ] (hi : HEq iF iF')
    (s s' : C₀ ⥤ C) (hs : s = s') (t t' : D₀ ⥤ D) (ht : t = t') (pull : C₀ ⥤ D₀)
    (c : s ⋙ F ≅ pull ⋙ t) (c' : s' ⋙ F' ≅ pull ⋙ t') (hc : HEq c c')
    (L L' : C₀) (hL : L = L') (M M' : D₀) (hM : M = M')
    (e : pull.obj L ≅ M) (e' : pull.obj L' ≅ M') (he : HEq e e') (b : ℤ) :
    HEq (Etale.p1DecompositionShiftedComparison F s t pull c L M e b)
      (Etale.p1DecompositionShiftedComparison F' s' t' pull c' L' M' e' b) := by
  subst hF hs ht hL hM
  cases hi
  cases hc
  cases he
  rfl

/-- The two single-degree comparisons for the etale inverse image agree. The degree-zero
embeddings are matched through `ordinaryFiniteSingleFunctor_eq`, never by unfolding them
against each other, which the kernel does only at great cost. -/
private theorem singlePullbackIso_heq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    HEq (Etale.ordinaryFiniteSinglePullbackIso A f)
      (Etale.singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} A) f) := by
  unfold Etale.ordinaryFiniteSinglePullbackIso Etale.singleFunctorCompLeftDerivedUpperStarIso
    Functor.singleFunctorCompLeftDerivedFunctorIso
  exact whiskerLeft_trans_heq _ _ (Etale.ordinaryFiniteSingleFunctor_eq A Y) _ _ _ _ rfl rfl
    _ _ HEq.rfl _ _ (congrArg (fun F ↦ Etale.upperStar (ModuleCat.{u + 1} A) f ⋙ F)
      ((Etale.ordinaryFiniteSingleFunctor_eq A X).trans rfl)) _ _
    ((heq_of_eq (Etale.ordinaryFiniteSingleExactPullbackIso_eq A f)).trans HEq.rfl)

private theorem shiftedLinePullback_eq (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : Etale.OrdinaryFiniteTwistTransport A N hA)
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hY : IsUnit (N : Γ(Y, ⊤))) :
    Etale.ordinaryFiniteShiftedLinePullback A N hA t f hY =
      Etale.p1DecompositionTwistPullback A N hN hA f hY 1 2 := by
  have hl := linePullback_eq A N hN hA t f hY
  unfold Etale.ordinaryFiniteShiftedLinePullback Etale.p1DecompositionTwistPullback
  rw [shiftedSinglePullbackIsoWith_eq, hl]
  exact eq_of_heq (shiftedComparison_heq _ _ rfl
    (iF := Etale.commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f)
    (iF' := Etale.commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f) HEq.rfl _ _
    ((Etale.ordinaryFiniteSingleFunctor_eq A Y).trans rfl) _ _
    ((Etale.ordinaryFiniteSingleFunctor_eq A X).trans rfl) _ _ _ (singlePullbackIso_heq A f)
    _ _ rfl _ _ rfl _ _ HEq.rfl 2)

private theorem chern_unique (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤)))
    (c : Etale.ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (hc : Etale.ordinaryFiniteP1ChernSpec A N hA S
      (affineTraceProjectiveInvertible N S hS) c) :
    c = (Etale.projectiveLineTraceDatum N hN A hA S hS).chern := by
  let : IsLocallyNoetherian (ProjectiveLine S) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveLine S ↘ S)
  let : CompactSpace (ProjectiveLine S) :=
    QuasiCompact.compactSpace_of_compactSpace (ProjectiveLine S ↘ S)
  exact (Etale.existsUnique_ordinaryFiniteP1Chern A N hA S
    (affineTraceProjectiveInvertible N S hS)).unique hc
      (Etale.projectiveLineTraceDatum N hN A hA S hS).chern_spec

set_option linter.flexible false in
private theorem compared_biprod_square
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    [Preadditive C] [Preadditive D] [Preadditive E] [Preadditive H]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    [HasBinaryBiproducts E] [HasBinaryBiproducts H]
    (F : C ⥤ D) (P : D ⥤ H) (Q : C ⥤ E) (G : E ⥤ H)
    [F.Additive] [P.Additive] [Q.Additive] [G.Additive]
    (α : F ⋙ P ≅ Q ⋙ G) (X Y : C) (X' Y' : E)
    (e : Q.obj X ⟶ X') (e' : Q.obj Y ⟶ Y') :
    P.map (biprod.desc (F.map biprod.inl) (F.map biprod.inr)) ≫
      α.hom.app (X ⊞ Y) ≫ G.map
        (biprod.lift (Q.map biprod.fst ≫ e) (Q.map biprod.snd ≫ e')) =
    biprod.lift (P.map biprod.fst ≫ α.hom.app X ≫ G.map e)
      (P.map biprod.snd ≫ α.hom.app Y ≫ G.map e') ≫
        biprod.desc (G.map biprod.inl) (G.map biprod.inr) := by
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts P
  apply (cancel_epi (P.mapBiprod (F.obj X) (F.obj Y)).inv).mp
  apply biprod.hom_ext'
  · simp only [Functor.mapBiprod_inv, biprod.inl_desc_assoc,
      ← Functor.map_comp_assoc, biprod.inl_desc]
    rw [reassoc_of% (α.hom.naturality (biprod.inl : X ⟶ X ⊞ Y))]
    simp [← Functor.map_comp_assoc]
    rw [← G.map_comp, ← G.map_comp]
    congr 1
    apply biprod.hom_ext <;> simp [← Functor.map_comp_assoc]
  · simp only [Functor.mapBiprod_inv, biprod.inr_desc_assoc,
      ← Functor.map_comp_assoc, biprod.inr_desc]
    rw [reassoc_of% (α.hom.naturality (biprod.inr : Y ⟶ X ⊞ Y))]
    simp [← Functor.map_comp_assoc]
    rw [← G.map_comp, ← G.map_comp]
    congr 1
    apply biprod.hom_ext <;> simp [← Functor.map_comp_assoc]

private theorem mate_app_homEquiv
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ H} {R' : H ⥤ E}
    {G : C ⥤ E} {F : D ⥤ H} (a : L ⊣ R) (b : L' ⊣ R')
    (α : G ⋙ L' ⟶ L ⋙ F) (K : D) :
    (mateEquiv a b α).app K = b.homEquiv _ _
      (α.app (R.obj K) ≫ F.map (a.counit.app K)) := by
  simp [mateEquiv_apply, Adjunction.homEquiv_unit]

private theorem pullComparison_eq (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    geoP1PullComparison A f = BoundaryComparison.pullbackSquare (ModuleCat.{u + 1} A) f := by
  unfold geoP1PullComparison BoundaryComparison.pullbackSquare
    leftDerivedUpperStarIsoMapDerivedCategory Etale.leftDerivedUpperStarIsoMapDerivedCategory
  rfl

private theorem pushComparison_mate (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (K : Etale.DerivedCategoryModule A X) :
    geoP1PushComparison A f K =
      (BoundaryComparison.directImageMate (ModuleCat.{u + 1} A) f).app K := by
  unfold geoP1PushComparison BoundaryComparison.directImageMate
  rw [mate_app_homEquiv]
  rw [pullComparison_eq]
  rfl

private theorem pushComparison_eq (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : Etale.DerivedCategoryModule A X) (hK : ∃ n : ℤ, K.IsGE n) :
    geoP1PushComparison A f K = (spDirectImageComparisonIso A f K hK).hom := by
  rw [sp_comparison_hom, pushComparison_mate]

private def exactPullComparison (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    geoP1Comparison A Y ⋙ geoP1Pullback A f ≅
      (Etale.upperStar (ModuleCat.{u + 1} A) f).mapDerivedCategory ⋙ geoP1Comparison A X :=
  geoP1PullComparison A f ≪≫ Functor.isoWhiskerRight
    (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) f) _

private theorem pushComparison_naturality (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    {K L : Etale.DerivedCategoryModule A X} (v : K ⟶ L) :
    (geoP1Comparison A Y).map ((Etale.ordinaryFinitePushforward A f).map v) ≫
        geoP1PushComparison A f L =
      geoP1PushComparison A f K ≫ (geoP1Pushforward A f).map
        ((geoP1Comparison A X).map v) := by
  rw [pushComparison_mate, pushComparison_mate]
  simpa only [Functor.comp_map, Functor.comp_obj, BoundaryComparison.comparison,
    BoundaryComparison.etaleImage,
    BoundaryComparison.proetaleImage, geoP1Comparison, geoP1Pushforward,
    Etale.ordinaryFinitePushforward] using
      (BoundaryComparison.directImageMate (ModuleCat.{u + 1} A) f).naturality v

private theorem exactPullComparison_plus (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (exactPullComparison A f).app K.obj = (leftDerivedUpperStarComparisonIso f A).symm.app K := by
  let σ := comparisonUpperStarCompUpperStarIso (ModuleCat.{u + 1} A) f
  have hs : (Functor.mapDerivedCategoryNatIso σ.symm).inv =
      (Functor.mapDerivedCategoryNatIso σ).hom := by
    exact (Functor.mapDerivedCategoryNatIso_symm σ.symm).symm
  apply Iso.ext
  simp only [Iso.app_hom, Iso.app_inv, exactPullComparison, geoP1PullComparison,
    leftDerivedUpperStarComparisonIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerLeft_inv,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, NatTrans.comp_app,
    Functor.mapDerivedCategoryPlusCompatibility, Iso.refl_inv, NatTrans.id_app,
    Functor.map_comp, Category.assoc, leftDerivedUpperStarIsoMapDerivedCategory,
    Etale.leftDerivedUpperStarIsoMapDerivedCategory]
  change _ = _ ≫ _ ≫ (Functor.mapDerivedCategoryNatIso σ.symm).inv.app _ ≫ _
  rw [hs]
  dsimp only [geoP1Comparison, Functor.comp_obj, DerivedCategory.Plus.ι]
  try simp only [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
    Category.comp_id]
  erw [CategoryTheory.Functor.map_id, Category.comp_id]
  rfl

private theorem pushComparison_plus (A : Type (u + 1)) [CommRing A] [Finite A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (geoP1Comparison A Y).map
        ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctorPlusCompatibility.hom.app K) ≫
      geoP1PushComparison A f K.obj =
    (rightDerivedLowerStarComparisonIso' f (ModuleCat.{u + 1} A)).hom.app K := by
  rw [pushComparison_eq A f K.obj K.property]
  exact proper_comparison_normalization A f K

private theorem exact_exchangeComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {X' X Y' Y : Scheme.{u}} {g' : X' ⟶ X} {f' : X' ⟶ Y'}
    {f : X ⟶ Y} {g : Y' ⟶ Y} [QuasiCompact f] [QuasiSeparated f]
    [QuasiCompact f'] [QuasiSeparated f'] (sq : IsPullback g' f' f g)
    (K : DerivedCategory.Plus (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (exactPullComparison A g).hom.app
        ((Etale.lowerStar (ModuleCat.{u + 1} A) f).rightDerivedFunctor.obj K.obj) ≫
      (geoP1Comparison A Y').map
        ((Etale.exactDerivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app K.obj) ≫
      geoP1PushComparison A f'
        ((Etale.upperStar (ModuleCat.{u + 1} A) g').mapDerivedCategory.obj K.obj) =
    (geoP1Pullback A g).map (geoP1PushComparison A f K.obj) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq.toCommSq).app
        ((geoP1Comparison A X).obj K.obj) ≫
      (geoP1Pushforward A f').map ((exactPullComparison A g').hom.app K.obj) := by
  let C := ModuleCat.{u + 1} A
  let r := (Etale.lowerStar C f).rightDerivedFunctorPlusCompatibility.hom.app K
  let K' := (Etale.upperStar C g').mapDerivedCategoryPlus.obj K
  have hb := comparison_derivedBaseChangeMap A sq K
  simp only [baseChangeSourceComparisonIso, baseChangeTargetComparisonIso,
    Iso.trans_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.comp_app] at hb
  have hn := congrArg (fun z ↦
    (leftDerivedUpperStarComparisonIso g A).inv.app
        ((Etale.lowerStar C f).rightDerivedFunctorPlus.obj K) ≫ z ≫
      (geoP1Pushforward A f').map ((leftDerivedUpperStarComparisonIso g' A).inv.app K)) hb
  dsimp only [geoP1Pushforward, C] at hn
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app,
    Iso.inv_hom_id_app_assoc, CategoryTheory.Functor.map_id, Category.comp_id] at hn
  have he := Etale.proper_exchange_plus C sq.toCommSq K
  rw [← Etale.baseChange_eq_derivedBaseChangeMapPlus] at he
  apply (cancel_epi ((geoP1Pullback A g).map ((geoP1Comparison A Y).map r))).mp
  have hnat := (exactPullComparison A g).hom.naturality r
  dsimp only [Functor.comp_map, Functor.comp_obj, C] at hnat
  simp only [← Functor.map_comp_assoc]
  rw [pushComparison_plus A f K]
  erw [reassoc_of% hnat]
  erw [← (geoP1Comparison A Y').map_comp_assoc, ← he]
  simp only [Functor.map_comp, Category.assoc]
  dsimp only [C, K', Functor.mapDerivedCategoryPlus, ObjectProperty.lift,
    Functor.comp_obj, ObjectProperty.ι_obj] at *
  erw [pushComparison_plus A f'
    ((Etale.upperStar (ModuleCat.{u + 1} A) g').mapDerivedCategoryPlus.obj K)]
  have hq := congrArg Iso.hom
    (exactPullComparison_plus A g ((Etale.lowerStar C f).rightDerivedFunctorPlus.obj K))
  have hq' := congrArg Iso.hom (exactPullComparison_plus A g' K)
  change (exactPullComparison A g).hom.app _ = _ at hq
  change (exactPullComparison A g').hom.app _ = _ at hq'
  rw [hq, hq']
  simpa only [Category.comp_id, geoP1Pullback, geoP1Pushforward, geoP1Comparison,
    C, Iso.app_hom, Iso.symm_hom, Functor.mapDerivedCategoryPlus, ObjectProperty.lift,
    Functor.comp_obj, ObjectProperty.ι_obj] using hn

private theorem exchangeComparison (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (g : S' ⟶ S)
    (K : DerivedCategory.Plus
      (Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} A))) :
    (geoP1PullComparison A g).hom.app
        ((Etale.ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj K.obj) ≫
      (geoP1Comparison A S').map (Etale.ordinaryFiniteP1Exchange A g K.obj) ≫
      geoP1PushComparison A (ProjectiveLine S' ↘ S')
        ((Etale.ordinaryFinitePullback A
          (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).obj K.obj) =
    (geoP1Pullback A g).map (geoP1PushComparison A (ProjectiveLine S ↘ S) K.obj) ≫
      geoP1Exchange A g ((geoP1Comparison A (ProjectiveLine S)).obj K.obj) ≫
      (geoP1Pushforward A (ProjectiveLine S' ↘ S')).map
        ((geoP1PullComparison A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom.app K.obj) := by
  let gp := ProjectiveSpace.map (ULift.{u} (Fin 2)) g
  let q' := ProjectiveLine S' ↘ S'
  let e := (Etale.leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) gp)
  have h := exact_exchangeComparison A (ProjectiveSpace.isPullback_map
    (ULift.{u} (Fin 2)) g) K
  have hn := pushComparison_naturality A q' (e.inv.app K.obj)
  have h' := congrArg (fun z ↦ z ≫ (geoP1Pushforward A q').map
    ((geoP1Comparison A (ProjectiveLine S')).map (e.inv.app K.obj))) h
  simp only [exactPullComparison, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Category.assoc] at h'
  dsimp only [gp, q'] at hn
  rw [← hn] at h'
  dsimp only [gp, q', e] at h'
  simp only [← Functor.map_comp, Category.assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id] at h'
  erw [Category.comp_id] at h'
  simpa only [Etale.ordinaryFiniteP1Exchange, geoP1Exchange,
    Etale.ordinaryFinitePushforward, Etale.ordinaryFinitePullback,
    Functor.map_comp, CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc] using h'

private theorem compared_map_square (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (g : S' ⟶ S)
    (K : DerivedCategory.Plus
      (Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K' : Etale.DerivedCategoryModule A (ProjectiveLine S'))
    (U : Etale.DerivedCategoryModule A S) (U' : Etale.DerivedCategoryModule A S')
    (d : U ⟶ (Etale.ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj K.obj)
    (d' : U' ⟶ (Etale.ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).obj K')
    (e : (Etale.ordinaryFinitePullback A g).obj U ⟶ U')
    (c : (Etale.ordinaryFinitePullback A
      (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).obj K.obj ⟶ K')
    (hd : (Etale.ordinaryFinitePullback A g).map d ≫
      Etale.ordinaryFiniteP1Exchange A g K.obj ≫
        (Etale.ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map c = e ≫ d') :
    (geoP1Pullback A g).map
        ((geoP1Comparison A S).map d ≫ geoP1PushComparison A (ProjectiveLine S ↘ S) K.obj) ≫
      geoP1Exchange A g ((geoP1Comparison A (ProjectiveLine S)).obj K.obj) ≫
        (geoP1Pushforward A (ProjectiveLine S' ↘ S')).map
          ((geoP1PullComparison A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom.app K.obj ≫
            (geoP1Comparison A (ProjectiveLine S')).map c) =
    ((geoP1PullComparison A g).hom.app U ≫ (geoP1Comparison A S').map e) ≫
      (geoP1Comparison A S').map d' ≫ geoP1PushComparison A (ProjectiveLine S' ↘ S') K' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [← reassoc_of% (exchangeComparison A g K)]
  erw [reassoc_of% ((geoP1PullComparison A g).hom.naturality d)]
  rw [← pushComparison_naturality A (ProjectiveLine S' ↘ S') c]
  simp only [← Functor.map_comp_assoc]
  rw [hd]

private theorem compared_sum_square (A : Type (u + 1)) [CommRing A] [Finite A]
    {S' S : Scheme.{u}} (g : S' ⟶ S)
    (K : DerivedCategory.Plus
      (Sheaf (ProjectiveLine S).smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K' : Etale.DerivedCategoryModule A (ProjectiveLine S'))
    (U V : Etale.DerivedCategoryModule A S) (U' V' : Etale.DerivedCategoryModule A S')
    (d : (U ⊞ V) ⟶ (Etale.ordinaryFinitePushforward A (ProjectiveLine S ↘ S)).obj K.obj)
    (d' : (U' ⊞ V') ⟶ (Etale.ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).obj K')
    (e : (Etale.ordinaryFinitePullback A g).obj U ⟶ U')
    (e' : (Etale.ordinaryFinitePullback A g).obj V ⟶ V')
    (c : (Etale.ordinaryFinitePullback A
      (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).obj K.obj ⟶ K')
    (hd : (Etale.ordinaryFinitePullback A g).map d ≫
      Etale.ordinaryFiniteP1Exchange A g K.obj ≫
        (Etale.ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map c =
      biprod.lift ((Etale.ordinaryFinitePullback A g).map biprod.fst ≫ e)
        ((Etale.ordinaryFinitePullback A g).map biprod.snd ≫ e') ≫ d') :
    (geoP1Pullback A g).map
        (geoP1SumComparison A S U V ≫ (geoP1Comparison A S).map d ≫
          geoP1PushComparison A (ProjectiveLine S ↘ S) K.obj) ≫
      geoP1Exchange A g ((geoP1Comparison A (ProjectiveLine S)).obj K.obj) ≫
        (geoP1Pushforward A (ProjectiveLine S' ↘ S')).map
          ((geoP1PullComparison A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom.app K.obj ≫
            (geoP1Comparison A (ProjectiveLine S')).map c) =
    biprod.lift
        ((geoP1Pullback A g).map biprod.fst ≫
          (geoP1PullComparison A g).hom.app U ≫ (geoP1Comparison A S').map e)
        ((geoP1Pullback A g).map biprod.snd ≫
          (geoP1PullComparison A g).hom.app V ≫ (geoP1Comparison A S').map e') ≫
      geoP1SumComparison A S' U' V' ≫ (geoP1Comparison A S').map d' ≫
        geoP1PushComparison A (ProjectiveLine S' ↘ S') K' := by
  let : (geoP1Pullback A g).Additive :=
    Functor.additive_of_iso
      (leftDerivedUpperStarIsoMapDerivedCategory (ModuleCat.{u + 1} A) g).symm
  let : (Etale.ordinaryFinitePullback A g).Additive :=
    Etale.additive_leftDerivedUpperStar (ModuleCat.{u + 1} A) g
  have h := compared_map_square A g K K' (U ⊞ V) (U' ⊞ V') d d' _ c hd
  have hb := compared_biprod_square (geoP1Comparison A S) (geoP1Pullback A g)
    (Etale.ordinaryFinitePullback A g) (geoP1Comparison A S')
    (geoP1PullComparison A g) U V U' V' e e'
  simp only [Functor.map_comp, Category.assoc] at h ⊢
  rw [h]
  simpa only [geoP1SumComparison, Category.assoc] using
    congrArg (fun z ↦ z ≫ (geoP1Comparison A S').map d' ≫
      geoP1PushComparison A (ProjectiveLine S' ↘ S') K') hb

private theorem untwisted_square (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S]
    (g : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤))) :
    (geoP1Pullback A g).map (geoP1DecompositionMap A N hN hA S hS) ≫
      geoP1UnitExchange A g =
    geoP1SourceMap A N hN hA g hS ≫ geoP1DecompositionMap A N hN hA S' hS' := by
  obtain ⟨c, hc, _, hb⟩ := Etale.ordinaryFiniteP1Decomposition N hN A hA S hS
  rw [chern_unique A N hN hA S hS c hc] at hb
  obtain ⟨c', hc', _, hb⟩ := hb S' g
  rw [chern_unique A N hN hA S' hS' c' hc'] at hb
  simp only [Etale.p1DecompositionSourceMap, Etale.p1DecompositionBiprodMap] at hb
  have h := compared_sum_square A g
    ⟨Etale.ordinaryFiniteUnit A (ProjectiveLine S), 0, inferInstance⟩
    (Etale.ordinaryFiniteUnit A (ProjectiveLine S'))
    (Etale.ordinaryFiniteUnit A S) (Etale.p1DecompositionTwist A N hA S (-1) (-2))
    (Etale.ordinaryFiniteUnit A S') (Etale.p1DecompositionTwist A N hA S' (-1) (-2))
    (Etale.p1DecompositionMap A N hN hA S hS
      (Etale.projectiveLineTraceDatum N hN A hA S hS).chern)
    (Etale.p1DecompositionMap A N hN hA S' hS'
      (Etale.projectiveLineTraceDatum N hN A hA S' hS').chern)
    (Etale.ordinaryFiniteUnitPullback A g).hom
    (Etale.p1DecompositionTwistPullback A N hN hA g hS (-1) (-2)).hom
    (Etale.ordinaryFiniteUnitPullback A
      (X := ProjectiveLine S') (Y := ProjectiveLine S)
      (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom
    hb
  simpa only [geoP1DecompositionMap, geoP1EtaleChern, geoP1UnitExchange,
    geoP1UnitPullback, geoP1TwistPullback, geoP1SourceMap, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc,
    Etale.p1DecompositionSourceMap, Etale.p1DecompositionBiprodMap] using h

private theorem twisted_square (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S' S : Scheme.{u}} [IsNoetherian S'] [IsNoetherian S]
    (g : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤))) (hS' : IsUnit (N : Γ(S', ⊤))) :
    (geoP1Pullback A g).map (geoP1TwistedMap A N hN hA S hS) ≫
        geoP1TwistExchange A N hN hA g hS =
      biprod.lift
        ((geoP1Pullback A g).map biprod.fst ≫ (geoP1TwistPullback A N hN hA g hS 1 2).hom)
        ((geoP1Pullback A g).map biprod.snd ≫ (geoP1UnitPullback A g).hom) ≫
      geoP1TwistedMap A N hN hA S' hS' := by
  have hb := (Etale.ordinaryFiniteP1BaseChange_of_normalization N hN A hA
    (Etale.projectiveLineTraceTransport N hN A hA)
    (Etale.projectiveLineTraceDatum N hN A hA) g hS hS').1
  simp only [Etale.ordinaryFiniteP1DecompositionSourceMap,
    shiftedLinePullback_eq A N hN hA] at hb
  have hK : (Etale.p1DecompositionTwist A N hA (ProjectiveLine S) 1 2).IsGE (-2) :=
    DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2) (by decide)
  have h := compared_sum_square A g
    ⟨Etale.p1DecompositionTwist A N hA (ProjectiveLine S) 1 2, -2, hK⟩
    (Etale.p1DecompositionTwist A N hA (ProjectiveLine S') 1 2)
    (Etale.p1DecompositionTwist A N hA S 1 2) (Etale.ordinaryFiniteUnit A S)
    (Etale.p1DecompositionTwist A N hA S' 1 2) (Etale.ordinaryFiniteUnit A S')
    _ _ (Etale.p1DecompositionTwistPullback A N hN hA g hS 1 2).hom
    (Etale.ordinaryFiniteUnitPullback A g).hom
    (Etale.p1DecompositionTwistPullback A N hN hA
      (X := ProjectiveLine S') (Y := ProjectiveLine S)
      (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)
      (affineTraceProjectiveInvertible N S hS) 1 2).hom hb
  simpa only [geoP1TwistedMap, geoP1TwistExchange, geoP1UnitPullback,
    geoP1Twist, geoP1Unit, Etale.p1DecompositionTwist, Etale.ordinaryFiniteLine,
    Scheme.finiteEtaleTateSheaf, Scheme.finiteEtaleTateTwist,
    geoP1TwistPullback, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    Category.assoc] using h

private theorem sumComparison_isIso (A : Type (u + 1)) [CommRing A] (S : Scheme.{u})
    (K L : Etale.DerivedCategoryModule A S) : IsIso (geoP1SumComparison A S K L) := by
  let F := geoP1Comparison A S
  let := preservesBinaryBiproducts_of_preservesBinaryCoproducts F
  change IsIso (biprod.desc (F.map biprod.inl) (F.map biprod.inr))
  change IsIso (F.mapBiprod K L).inv
  infer_instance

private theorem decomposition_isIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    IsIso (geoP1DecompositionMap A N hN hA S hS) := by
  let d := Etale.projectiveLineTraceDatum N hN A hA S hS
  have hi : IsIso (Etale.p1DecompositionMap A N hN hA S hS d.chern) := by
    apply Etale.isIso_p1DecompositionMap_of_twisted A N hN hA
      (Etale.projectiveLineTraceTransport N hN A hA)
    rw [← d.decomposition_hom]
    infer_instance
  have hs := sumComparison_isIso A S (Etale.ordinaryFiniteUnit A S)
    (Etale.p1DecompositionTwist A N hA S (-1) (-2))
  have hp : IsIso (geoP1PushComparison A (ProjectiveLine S ↘ S)
      (Etale.ordinaryFiniteUnit A (ProjectiveLine S))) := by
    rw [pushComparison_eq A _ _ ⟨0, inferInstance⟩]
    infer_instance
  unfold geoP1DecompositionMap geoP1EtaleChern
  change IsIso (geoP1SumComparison A S _ _ ≫
    (geoP1Comparison A S).map (Etale.p1DecompositionMap A N hN hA S hS d.chern) ≫ _)
  infer_instance

private theorem twisted_isIso (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))) :
    IsIso (geoP1TwistedMap A N hN hA S hS) := by
  have hs := sumComparison_isIso A S
    (Etale.p1DecompositionTwist A N hA S 1 2) (Etale.ordinaryFiniteUnit A S)
  have hp : IsIso (geoP1PushComparison A (ProjectiveLine S ↘ S)
      (Etale.p1DecompositionTwist A N hA (ProjectiveLine S) 1 2)) := by
    rw [pushComparison_eq A _ _ ⟨-2, ?_⟩]
    swap
    · exact DerivedCategory.TStructure.t.isGE_shift _ 0 2 (-2) (by decide)
    infer_instance
  have hp' : IsIso (geoP1PushComparison A (ProjectiveLine S ↘ S)
      ((Etale.ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)) := hp
  unfold geoP1TwistedMap
  let := hs
  let := hp'
  infer_instance

private theorem trace_square_of_decomposition
    {C D : Type*} [Category C] [Category D] [HasZeroMorphisms C] [HasZeroMorphisms D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D]
    (F : C ⥤ D) {X Y Z : C} {X' Y' Z' : D}
    (b : (X ⊞ Y) ≅ Z) (b' : (X' ⊞ Y') ≅ Z')
    (a : F.obj X ⟶ X') (e : F.obj Y ⟶ Y') (k : F.obj Z ⟶ Z')
    (h : F.map b.hom ≫ k =
      biprod.lift (F.map biprod.fst ≫ a) (F.map biprod.snd ≫ e) ≫ b'.hom) :
    F.map (b.inv ≫ biprod.snd) ≫ e = k ≫ b'.inv ≫ biprod.snd := by
  apply (cancel_epi (F.map b.hom)).mp
  rw [← Functor.map_comp_assoc, b.hom_inv_id_assoc]
  symm
  calc
    F.map b.hom ≫ k ≫ b'.inv ≫ biprod.snd =
        (F.map b.hom ≫ k) ≫ b'.inv ≫ biprod.snd := by rw [Category.assoc]
    _ = _ := by rw [h, Category.assoc, b'.hom_inv_id_assoc, biprod.lift_snd]

/-- The canonical decomposition (G2) and the trace (G3), with every Noetherian
base change. The existential isomorphisms have their homs fixed to `geoP1TwistedMap`;
their inverses, hence the traces, are uniquely determined. The untwisted map is
fixed separately to the unit and the same Kummer Chern class.

Source: blueprint main-20261015, sec-six-functors-basics/sk-lem-geo-p1-cohomology,
(G2), (G3), proof steps 1--9; Stacks Project, Tag 0GL5
(blueprint: lemma-cohomology-projective-line-trace).

Proof:
1. Use the ordinary étale projective-line decomposition and the normalized trace
   datum. Chern-class injectivity identifies the decomposition's class with the
   chosen trace class. Uniqueness of normalized Tate transport identifies its
   positive-line pullback with the signed-twist pullback used here.
2. The exact comparison preserves biproducts. Its direct-image counit mate is
   invertible on the degree-zero constant object and the positive line shifted
   by two, by the bounded-below direct-image comparison theorem. Thus both
   displayed decomposition maps are invertible.
3. Restrict the fixed étale/pro-étale exchange comparison from D+ to the
   unbounded derived category. Naturality of the pullback comparison and the
   direct-image mate transfers each étale decomposition square. The universal
   property of biproducts identifies the source maps with the displayed ones.
4. Choose each twisted isomorphism as asIso of its specified map. Invert the
   twisted base-change square and project to the constant second summand to
   obtain the stated trace equation. -/
theorem geoP1Cohomology (ℓ : ℕ) (hℓ : ℓ.Prime) (r : ℕ) (_hr : 0 < r)
    (A : Type (u + 1)) [CommRing A] [Finite A] (hA : ((ℓ ^ r : ℕ) : A) = 0) :
    ∃ b : ∀ (S : Scheme.{u}) [IsNoetherian S]
      (_hS : IsUnit ((ℓ ^ r : ℕ) : Γ(S, ⊤))),
        (geoP1Twist A (ℓ ^ r) hA S 1 2 ⊞ geoP1Unit A S) ≅
          (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
            (geoP1Twist A (ℓ ^ r) hA (ProjectiveLine S) 1 2),
      (∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit ((ℓ ^ r : ℕ) : Γ(S, ⊤))),
        IsIso (geoP1DecompositionMap A (ℓ ^ r) (pow_pos hℓ.pos r) hA S hS) ∧
        (b S hS).hom = geoP1TwistedMap A (ℓ ^ r) (pow_pos hℓ.pos r) hA S hS) ∧
      ∀ (S' S : Scheme.{u}) [IsNoetherian S'] [IsNoetherian S] (g : S' ⟶ S)
        (hS : IsUnit ((ℓ ^ r : ℕ) : Γ(S, ⊤)))
        (hS' : IsUnit ((ℓ ^ r : ℕ) : Γ(S', ⊤))),
        ((geoP1Pullback A g).map
            (geoP1DecompositionMap A (ℓ ^ r) (pow_pos hℓ.pos r) hA S hS) ≫
          geoP1UnitExchange A g =
          geoP1SourceMap A (ℓ ^ r) (pow_pos hℓ.pos r) hA g hS ≫
            geoP1DecompositionMap A (ℓ ^ r) (pow_pos hℓ.pos r) hA S' hS') ∧
        ((geoP1Pullback A g).map (geoP1Trace A (ℓ ^ r) hA S (b S hS)) ≫
            (geoP1UnitPullback A g).hom =
          geoP1TwistExchange A (ℓ ^ r) (pow_pos hℓ.pos r) hA g hS ≫
            geoP1Trace A (ℓ ^ r) hA S' (b S' hS'))  := by
  let N := ℓ ^ r
  have hN : 0 < N := pow_pos hℓ.pos r
  let b : ∀ (S : Scheme.{u}) [IsNoetherian S] (hS : IsUnit (N : Γ(S, ⊤))),
      (geoP1Twist A N hA S 1 2 ⊞ geoP1Unit A S) ≅
        (geoP1Pushforward A (ProjectiveLine S ↘ S)).obj
          (geoP1Twist A N hA (ProjectiveLine S) 1 2) := fun S _ hS ↦ by
    letI := twisted_isIso A N hN hA S hS
    exact asIso (geoP1TwistedMap A N hN hA S hS)
  refine ⟨b, ?_, ?_⟩
  · intro S _ hS
    exact ⟨decomposition_isIso A N hN hA S hS, rfl⟩
  · intro S' S _ _ g hS hS'
    refine ⟨untwisted_square A N hN hA g hS hS', ?_⟩
    exact trace_square_of_decomposition (geoP1Pullback A g) (b S hS) (b S' hS')
      (geoP1TwistPullback A N hN hA g hS 1 2).hom (geoP1UnitPullback A g).hom
      (geoP1TwistExchange A N hN hA g hS) (twisted_square A N hN hA g hS hS')

end AlgebraicGeometry.ProEtale
