/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DecompositionMapsSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteP1TwistedUnitBaseChange
import all WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
import all WeilConjectures.AlgebraicGeometry.Relative.RelativeKummerExchangeGeneratorsSupplement
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleSinglePullbackComparisonsSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullback
import all Mathlib.AlgebraicGeometry.Sites.Etale
import all Mathlib.AlgebraicGeometry.Scheme
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import all WeilConjectures.AlgebraicGeometry.Sites.Kummer
import all Mathlib.Algebra.Module.ZMod
import all Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import all Mathlib.CategoryTheory.Sites.Monoidal
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import all WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import all WeilConjectures.CategoryTheory.RingedSiteModules
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import all WeilConjectures.AlgebraicGeometry.EtaleSheaves
import all WeilConjectures.AlgebraicGeometry.DerivedCategories
import all WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
import all WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
import all WeilConjectures.CategoryTheory.AlgebraicInverseImage
import all Mathlib.Algebra.Category.ModuleCat.Sheaf
import all Mathlib.Algebra.Category.Ring.Limits
import all Mathlib.Algebra.Category.Grp.Limits
import all Mathlib.CategoryTheory.Sites.Whiskering
import all Mathlib.CategoryTheory.Sites.Equivalence
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.CategoryTheory.Functor.Derived.LeftDerived
import all WeilConjectures.Algebra.Homology.KFlatResolution
import all WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatQuasiIso
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
import all WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
import all Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
import all Mathlib.Algebra.Category.Grp.FilteredColimits
import all Mathlib.Algebra.Homology.BifunctorShift
import all Mathlib.Algebra.Homology.QuasiIso
import all Mathlib.CategoryTheory.Comma.StructuredArrow.Small
import all Mathlib.CategoryTheory.Limits.EssentiallySmall
import all WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
import all WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
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
import all Mathlib.CategoryTheory.Sites.Limits
import all Mathlib.CategoryTheory.Adjunction.Limits
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
import all Mathlib.CategoryTheory.Sites.EpiMono
import all Mathlib.CategoryTheory.Adjunction.Additive
import all Mathlib.Algebra.Category.Grp.EpiMono
import all Mathlib.Algebra.Category.Grp.Abelian
import all Mathlib.CategoryTheory.Sites.Abelian
import all WeilConjectures.Algebra.Category.ModuleCat.Sheaf.MonoidalClosed
import all WeilConjectures.Algebra.Homology.Site.SiteDerivedTensorDescent
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.TensorShiftIso
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import all WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackBase
import all WeilConjectures.ConstructibleSheaf.Defs
import all WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import all WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTensorFamily
import all WeilConjectures.CategoryTheory.NormalizedSignedTensorPowers
import all WeilConjectures.CategoryTheory.Monoidal.IntTensorFamily
import all WeilConjectures.CategoryTheory.IntTensorFamilyIso
import all Mathlib.CategoryTheory.Monoidal.Braided.Basic
import all WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import all WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import all WeilConjectures.ConstructibleSheaf.Pullback
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.LocallyTrivialInverse
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.Surjective
import all WeilConjectures.SixFunctors.Etale.UpperLowerStar.MonoidalComp
import all WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula.Unit
import all WeilConjectures.AlgebraicGeometry.EtaleFiniteTwistPullbackRest
import all Mathlib.CategoryTheory.Abelian.Refinements
import all Mathlib.Algebra.Homology.ShortComplex.Exact
import all WeilConjectures.AlgebraicGeometry.ProperProjectionFormula
import all WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection
import all WeilConjectures.CategoryTheory.Monoidal.EtaleDerivedTensorSymmetrySupplement
import all WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import all Mathlib.AlgebraicGeometry.Morphisms.Proper
import all Mathlib.AlgebraicGeometry.Noetherian
import all Mathlib.Topology.Defs.Filter
import all WeilConjectures.AlgebraicGeometry.EtaleInverseImageModulesExact
import all WeilConjectures.SixFunctors.Etale.Derived.Tensor
import all WeilConjectures.AlgebraicGeometry.ExactUnboundedExchange
import all WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import all WeilConjectures.SixFunctors.BaseChange.Square
import all WeilConjectures.SixFunctors.Etale.Derived.Shift
import all WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
import all WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import all Mathlib.CategoryTheory.Adjunction.Whiskering
import all WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFunctor.SingleFunctor
import all WeilConjectures.CategoryTheory.DerivedCategory.Shift.ExactFunctor
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import WeilConjectures.AlgebraicGeometry.FiniteTwistDerivedEvaluationPullback
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DecompositionMapsSupplement
import WeilConjectures.AlgebraicGeometry.FiniteTwistShiftedPairingPullback
import WeilConjectures.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility
import WeilConjectures.SixFunctors.Etale.Derived.Invertible
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatSingleTensorCompatibilityDataSupplement
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorNaturality
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorAssociativity
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
import WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
import WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorSymmetry
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorFactorization
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorPullback
import WeilConjectures.AlgebraicGeometry.EtaleSingleHomotopyTensorPullback
import WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
import WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
import WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackCounit
import WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorHomotopyFactorization
import WeilConjectures.CategoryTheory.FlatPairingAssociativityAssembly
import Mathlib.CategoryTheory.Monoidal.Functor
import WeilConjectures.CategoryTheory.FlatPairingPullbackAssembly
import WeilConjectures.AlgebraicGeometry.DerivedPairingOppositeShiftsPullback
import WeilConjectures.AlgebraicGeometry.FiniteTwistDegreeZeroEvaluationPullback
import WeilConjectures.AlgebraicGeometry.FiniteTwistDegreeZeroEvaluationPairing
import WeilConjectures.AlgebraicGeometry.FiniteTwistFlatEvaluationPullback
import WeilConjectures.AlgebraicGeometry.FlatSinglePairingSymmetricPullback
import WeilConjectures.AlgebraicGeometry.DerivedPullbackTensorSymmetry
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Braided
import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteDerivedRightUnitPullback
import all WeilConjectures.AlgebraicGeometry.FiniteTwistShiftedFactorComparisons
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteSingleUnitNaturality
import WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekBaseChangeShift

/-! # Base change of the projective-line evaluation recipe
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u uB

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Etale

set_option linter.auxLemma false in
attribute [local instance 100000] DerivedCategoryModule._proof_1 DerivedCategoryModule._proof_2

set_option linter.auxLemma false in
attribute [local instance 100000]
  ordinaryFinitePullback._proof_1 ordinaryFinitePullback._proof_2
  ordinaryFinitePullback._proof_3 ordinaryFinitePullback._proof_4
  ordinaryFinitePullback._proof_5 ordinaryFinitePullback._proof_6
  ordinaryFinitePullback._proof_7 ordinaryFinitePullback._proof_8
  ordinaryFinitePullback._proof_9 ordinaryFinitePullback._proof_10
  ordinaryFinitePullback._proof_11 ordinaryFinitePullback._proof_12
  ordinaryFinitePullback._proof_13

@[reducible] private def pullback_shift (A : Type (u + 1)) [CommRing A]
    {X Y : Scheme.{u}} (f : X ⟶ Y) : (ordinaryFinitePullback A f).CommShift ℤ :=
  commShiftLeftDerivedUpperStar (ModuleCat.{u + 1} A) f

attribute [local instance] pullback_shift

attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero

attribute [local irreducible] singleFunctorPullbackMap
  upperStar Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor Functor.mapDerivedCategory

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors

private theorem signed_sheaf_comp (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hZ : IsUnit (N : Γ(Z, ⊤))) (hY : IsUnit (N : Γ(Y, ⊤)))
    (a : ℤ) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (upperStarComp (ModuleCat.{u + 1} A) f g fg hfg).hom.app _ ≫
        (upperStar (ModuleCat.{u + 1} A) f).map
          (p1DecompositionSheafPullback A N hN hA g hZ a).hom ≫
        (p1DecompositionSheafPullback A N hN hA f hY a).hom =
      (p1DecompositionSheafPullback A N hN hA fg hZ a).hom := by
  subst fg
  unfold p1DecompositionSheafPullback
  rw [p1DecompositionTwistTransport]
  exact (congrArg Iso.hom
    ((Scheme.finiteEtaleTwistPullbackData A N hN hA).laws.2.2.2.2.2.2.2.1
      g f hZ hY ((map_natCast f.appTop.hom N) ▸ hY.map f.appTop.hom) a)).symm

private theorem single_map_comp
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g)
    (W : Sheaf Z.smallEtaleTopology B) (V : Sheaf Y.smallEtaleTopology B)
    (U : Sheaf X.smallEtaleTopology B)
    (a : (upperStar B g).obj W ⟶ V) (b : (upperStar B f).obj V ⟶ U)
    (d : (upperStar B fg).obj W ⟶ U)
    (hab : (upperStarComp B f g fg hfg).hom.app W ≫ (upperStar B f).map a ≫ b = d) :
    (leftDerivedUpperStarComp B f g fg hfg).hom.app
        ((DerivedCategory.singleFunctor _ 0).obj W) ≫
      (upperStar B f).leftDerivedFunctor.map (singleFunctorPullbackMap g a) ≫
        singleFunctorPullbackMap f b = singleFunctorPullbackMap fg d := by
  have h := leftDerivedUpperStar_map_singleFunctor_comp B f g fg hfg W a d b hab
  simpa only [singleFunctorPullbackMap, Category.assoc, Iso.hom_inv_id_app_assoc] using
    congrArg (fun z ↦ (leftDerivedUpperStarComp B f g fg hfg).hom.app _ ≫ z) h

private theorem shifted_single_square
    (B : Type uB) [Category.{u + 1} B] [Abelian B]
    [IsGrothendieckAbelian.{u + 1} B] [MonoidalCategory B] [MonoidalPreadditive B]
    [SymmetricCategory B] [MonoidalClosed B] [Abelian.HasFunctorialFlatResolution B]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : X' ⟶ X} {f : Y' ⟶ Y} (sq : CommSq g q' q f)
    (W : Sheaf Y.smallEtaleTopology B) (V : Sheaf X.smallEtaleTopology B)
    (V' : Sheaf Y'.smallEtaleTopology B) (U : Sheaf X'.smallEtaleTopology B)
    (lq : (upperStar B q).obj W ≅ V) (lg : (upperStar B g).obj V ≅ U)
    (lf : (upperStar B f).obj W ≅ V') (lq' : (upperStar B q').obj V' ≅ U)
    (ld : (upperStar B (g ≫ q)).obj W ⟶ U)
    (hqf : (upperStarComp B q' f (g ≫ q) sq.w).hom.app W ≫
      (upperStar B q').map lf.hom ≫ lq'.hom = ld)
    (hgq : (upperStarComp B g q).hom.app W ≫
      (upperStar B g).map lq.hom ≫ lg.hom = ld) (b : ℤ) :
    (derivedSquareUpperStarIso B sq).hom.app
        (((DerivedCategory.singleFunctor _ 0).obj W)⟦b⟧) ≫
      (upperStar B g).leftDerivedFunctor.map
        (p1DecompositionShiftedComparison (upperStar B q).leftDerivedFunctor
          (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
          (upperStar B q) (singleFunctorCompLeftDerivedUpperStarIso B q) W V lq b).hom ≫
      (p1DecompositionShiftedComparison (upperStar B g).leftDerivedFunctor
        (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
        (upperStar B g) (singleFunctorCompLeftDerivedUpperStarIso B g) V U lg b).hom =
    (upperStar B q').leftDerivedFunctor.map
        (p1DecompositionShiftedComparison (upperStar B f).leftDerivedFunctor
          (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
          (upperStar B f) (singleFunctorCompLeftDerivedUpperStarIso B f) W V' lf b).hom ≫
      (p1DecompositionShiftedComparison (upperStar B q').leftDerivedFunctor
        (DerivedCategory.singleFunctor _ 0) (DerivedCategory.singleFunctor _ 0)
        (upperStar B q') (singleFunctorCompLeftDerivedUpperStarIso B q') V' U lq' b).hom := by
  have hc₁ := single_map_comp B q' f (g ≫ q) sq.w W V' U lf.hom lq'.hom ld hqf
  have hc₂ := single_map_comp B g q (g ≫ q) rfl W V U lq.hom lg.hom ld hgq
  have e := shifted_square (upperStar B f).leftDerivedFunctor
    (upperStar B q').leftDerivedFunctor (upperStar B q).leftDerivedFunctor
    (upperStar B g).leftDerivedFunctor (upperStar B (g ≫ q)).leftDerivedFunctor
    (leftDerivedUpperStarComp B q' f (g ≫ q) sq.w)
    (leftDerivedUpperStarComp B g q)
    (singleFunctorPullbackMap f lf.hom) (singleFunctorPullbackMap q' lq'.hom)
    (singleFunctorPullbackMap q lq.hom) (singleFunctorPullbackMap g lg.hom)
    (singleFunctorPullbackMap (g ≫ q) ld) hc₁ hc₂ b
  simpa only [generic_shifted_pullback_hom, shiftedHom, derivedSquareUpperStarIso] using e

private theorem signed_square (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : X' ⟶ X} {f : Y' ⟶ Y} (sq : CommSq g q' q f)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hY' : IsUnit (N : Γ(Y', ⊤)))
    (hX : IsUnit (N : Γ(X, ⊤))) (a b : ℤ) :
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app
        (p1DecompositionTwist A N hA Y a b) ≫
      (ordinaryFinitePullback A g).map
        (p1DecompositionTwistPullback A N hN hA q hY a b).hom ≫
      (p1DecompositionTwistPullback A N hN hA g hX a b).hom =
    (ordinaryFinitePullback A q').map
        (p1DecompositionTwistPullback A N hN hA f hY a b).hom ≫
      (p1DecompositionTwistPullback A N hN hA q' hY' a b).hom := by
  dsimp only [p1DecompositionTwistPullback, ordinaryFinitePullback,
    p1DecompositionTwist, ordinaryFiniteDegreeZero]
  exact shifted_single_square (ModuleCat.{u + 1} A) sq
      (Scheme.finiteEtaleTateSheaf A N Y hA a)
      (Scheme.finiteEtaleTateSheaf A N X hA a)
      (Scheme.finiteEtaleTateSheaf A N Y' hA a)
      (Scheme.finiteEtaleTateSheaf A N X' hA a)
      (p1DecompositionSheafPullback A N hN hA q hY a)
      (p1DecompositionSheafPullback A N hN hA g hX a)
      (p1DecompositionSheafPullback A N hN hA f hY a)
      (p1DecompositionSheafPullback A N hN hA q' hY' a)
      (p1DecompositionSheafPullback A N hN hA (g ≫ q) hY a).hom
      (signed_sheaf_comp A N hN hA q' f hY hY' a (g ≫ q) sq.w)
      (signed_sheaf_comp A N hN hA g q hY hX a (g ≫ q) rfl) b

private theorem pairing_pullback
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    (T : C ⥤ C ⥤ C) (T' : D ⥤ D ⥤ D)
    {K P U L V : C} {P' U' L' V' : D}
    (r : K ⟶ (T.obj K).obj U) (k : K ⟶ P) (c : U ⟶ L)
    (ev : (T.obj P).obj L ⟶ V)
    (r' : F.obj K ⟶ (T'.obj (F.obj K)).obj U')
    (p : F.obj P ⟶ P') (u : F.obj U ⟶ U') (l : F.obj L ⟶ L')
    (v : F.obj V ⟶ V') (c' : U' ⟶ L') (ev' : (T'.obj P').obj L' ⟶ V')
    (dKU : F.obj ((T.obj K).obj U) ⟶ (T'.obj (F.obj K)).obj (F.obj U))
    (dKL : F.obj ((T.obj K).obj L) ⟶ (T'.obj (F.obj K)).obj (F.obj L))
    (dPL : F.obj ((T.obj P).obj L) ⟶ (T'.obj (F.obj P)).obj (F.obj L))
    (hnL : F.map ((T.obj K).map c) ≫ dKL =
      dKU ≫ (T'.obj (F.obj K)).map (F.map c))
    (hnK : F.map ((T.map k).app L) ≫ dPL =
      dKL ≫ (T'.map (F.map k)).app (F.obj L))
    (he : F.map ev ≫ v = dPL ≫ (T'.obj (F.obj P)).map l ≫
      (T'.map p).app L' ≫ ev')
    (hr : F.map r ≫ dKU ≫ (T'.obj (F.obj K)).map u = r')
    (hc : F.map c ≫ l = u ≫ c') :
    F.map (r ≫ (T.obj K).map c ≫ (T.map k).app L ≫ ev) ≫ v =
      r' ≫ (T'.obj (F.obj K)).map c' ≫ (T'.map (F.map k ≫ p)).app L' ≫ ev' := by
  simp only [Functor.map_comp, Category.assoc]
  rw [he, reassoc_of% hnK, reassoc_of% hnL]
  rw [← (T'.map (F.map k)).naturality_assoc l]
  rw [← (T'.obj (F.obj K)).map_comp_assoc, hc, Functor.map_comp]
  simp only [Category.assoc]
  rw [reassoc_of% hr]
  simp only [NatTrans.comp_app, Category.assoc]

private theorem recipe_pasting_point
    {C : Type*} [Category C] (T : C ⥤ C ⥤ C) {U L V K K₁ K₂ : C}
    (r : K ⟶ (T.obj K).obj U) (r₁ : K₁ ⟶ (T.obj K₁).obj U)
    (r₂ : K₂ ⟶ (T.obj K₂).obj U) (c : U ⟶ L) (ev : (T.obj V).obj L ⟶ U)
    (s : K ⟶ K₁) (b : K ⟶ K₂) (k₁ : K₁ ⟶ V) (k₂ : K₂ ⟶ V)
    (h₁ : s ≫ r₁ = r ≫ (T.map s).app U)
    (h₂ : b ≫ r₂ = r ≫ (T.map b).app U) (h : s ≫ k₁ = b ≫ k₂) :
    s ≫ r₁ ≫ (T.obj K₁).map c ≫ (T.map k₁).app L ≫ ev =
      b ≫ r₂ ≫ (T.obj K₂).map c ≫ (T.map k₂).app L ≫ ev := by
  have h₁' : s ≫ r₁ ≫ (T.obj K₁).map c ≫ (T.map k₁).app L ≫ ev =
      r ≫ (T.obj K).map c ≫ (T.map (s ≫ k₁)).app L ≫ ev := by
    rw [reassoc_of% h₁, ← (T.map s).naturality_assoc c]
    simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  have h₂' : b ≫ r₂ ≫ (T.obj K₂).map c ≫ (T.map k₂).app L ≫ ev =
      r ≫ (T.obj K).map c ≫ (T.map (b ≫ k₂)).app L ≫ ev := by
    rw [reassoc_of% h₂, ← (T.map b).naturality_assoc c]
    simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [h₁', h₂', h]

/-- Pullback preserves the evaluation recipe defining the negative-twist component. -/
theorem ordinaryFiniteP1_evaluationRecipe_baseChange
    (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    (t : OrdinaryFiniteTwistTransport A N hA)
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : X' ⟶ X} {f : Y' ⟶ Y} (sq : CommSq g q' q f)
    (hY : IsUnit (N : Γ(Y, ⊤))) (hY' : IsUnit (N : Γ(Y', ⊤)))
    (hX : IsUnit (N : Γ(X, ⊤))) (hX' : IsUnit (N : Γ(X', ⊤)))
    (c : ordinaryFiniteUnit A X ⟶ (ordinaryFiniteLine A N hA X)⟦(2 : ℤ)⟧)
    (c' : ordinaryFiniteUnit A X' ⟶ (ordinaryFiniteLine A N hA X')⟦(2 : ℤ)⟧)
    (hc : (ordinaryFinitePullback A g).map c ≫
        (ordinaryFiniteShiftedLinePullback A N hA t g hX).hom =
      (ordinaryFiniteUnitPullback A g).hom ≫ c') :
    let K := p1DecompositionTwist A N hA Y (-1) (-2)
    let K' := p1DecompositionTwist A N hA Y' (-1) (-2)
    let z := (derivedTensorSingleUnitIso ((ordinaryFinitePullback A q).obj K)).inv ≫
      ((ordinaryFiniteTensor A X).obj ((ordinaryFinitePullback A q).obj K)).map c ≫
      ((ordinaryFiniteTensor A X).map
        (p1DecompositionTwistPullback A N hN hA q hY (-1) (-2)).hom).app _ ≫
      p1DecompositionEvaluation A N hN hA X hX
    let z' := (derivedTensorSingleUnitIso ((ordinaryFinitePullback A q').obj K')).inv ≫
      ((ordinaryFiniteTensor A X').obj ((ordinaryFinitePullback A q').obj K')).map c' ≫
      ((ordinaryFiniteTensor A X').map
        (p1DecompositionTwistPullback A N hN hA q' hY' (-1) (-2)).hom).app _ ≫
      p1DecompositionEvaluation A N hN hA X' hX'
    (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app K ≫
      (ordinaryFinitePullback A g).map z ≫ (ordinaryFiniteUnitPullback A g).hom =
    (ordinaryFinitePullback A q').map
      (p1DecompositionTwistPullback A N hN hA f hY (-1) (-2)).hom ≫ z' := by
  dsimp only
  let K := p1DecompositionTwist A N hA Y (-1) (-2)
  let H := ordinaryFinitePullback A g
  let T := ordinaryFiniteTensor A X'
  let s := (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app K
  let b := (ordinaryFinitePullback A q').map
    (p1DecompositionTwistPullback A N hN hA f hY (-1) (-2)).hom
  let k := (p1DecompositionTwistPullback A N hN hA q hY (-1) (-2)).hom
  let k' := (p1DecompositionTwistPullback A N hN hA q' hY' (-1) (-2)).hom
  let p := (p1DecompositionTwistPullback A N hN hA g hX (-1) (-2)).hom
  let ev' := p1DecompositionEvaluation A N hN hA X' hX'
  have he := (finiteTwistDerivedEvaluation_pullback A N hN hA
    t g hX).1
  have hr := (finiteTwistDerivedEvaluation_pullback A N hN hA
    t g hX).2 ((ordinaryFinitePullback A q).obj K)
  have hp := pairing_pullback H (ordinaryFiniteTensor A X) T
    (derivedTensorSingleUnitIso ((ordinaryFinitePullback A q).obj K)).inv k c
    (p1DecompositionEvaluation A N hN hA X hX)
    (derivedTensorSingleUnitIso (H.obj ((ordinaryFinitePullback A q).obj K))).inv
    p (ordinaryFiniteUnitPullback A g).hom
    (ordinaryFiniteShiftedLinePullback A N hA t g hX).hom
    (ordinaryFiniteUnitPullback A g).hom c' ev' _ _ _
    (leftDerivedUpperStarTensorIso_hom_naturality_right g
      ((ordinaryFinitePullback A q).obj K) c)
    (leftDerivedUpperStarTensorIso_hom_naturality_left g k _)
    he hr hc
  rw [hp]
  have hs := signed_square A N hN hA sq hY hY' hX (-1) (-2)
  exact recipe_pasting_point T _ _ _ c' ev' s b (H.map k ≫ p) k'
    (ordinaryFiniteSingleUnit_naturality A X' s) (ordinaryFiniteSingleUnit_naturality A X' b) hs

end AlgebraicGeometry.Etale
