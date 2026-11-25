/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DecompositionMapsSupplement
import all WeilConjectures.AlgebraicGeometry.FiniteP1ChernAdjunctMate
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
import all WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackComp
import all WeilConjectures.AlgebraicGeometry.OrdinaryFiniteUnitPullbackHom
import all WeilConjectures.SixFunctors.Etale.Derived.LeftDerivedUpperStarSingle
import all WeilConjectures.ConstructibleSheaf.UpperStarConstantSheafComp
import all WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarAdjunctionCompat
import all WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate
import all WeilConjectures.SixFunctors.BaseChange.DerivedUnbounded
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
import all WeilConjectures.AlgebraicGeometry.FiniteTwistShiftedFactorComparisons
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1DecompositionMapsSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleSingleFunctorMonoidalCompatibility
import all WeilConjectures.SixFunctors.Etale.Derived.Invertible
import all WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import all WeilConjectures.AlgebraicGeometry.Etale.EtaleFlatSingleTensorCompatibilityDataSupplement
import all WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorNaturality
import all WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorAssociativity
import all WeilConjectures.Mathlib.CategoryTheory.Monoidal.Functor
import all WeilConjectures.AlgebraicGeometry.EtaleSingleCochainMonoidal
import all WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
import all WeilConjectures.CategoryTheory.GrothendieckAbelian.HasColimitsOfSize
import all WeilConjectures.FromJoel.Algebra.Homology.BifunctorSingle
import all WeilConjectures.Mathlib.Algebra.Homology.Monoidal
import all WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorSymmetry
import all WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorFactorization
import all WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorPullback
import all WeilConjectures.AlgebraicGeometry.EtaleSingleHomotopyTensorPullback
import all WeilConjectures.CategoryTheory.Monoidal.Instances.HomotopyCategory
import all WeilConjectures.Algebra.Homology.HomotopyCategory.MapMonoidal
import all WeilConjectures.AlgebraicGeometry.EtaleSinglePullbackCounit
import all WeilConjectures.AlgebraicGeometry.EtaleSingleTensoratorHomotopyFactorization
import all WeilConjectures.CategoryTheory.FlatPairingAssociativityAssembly
import all Mathlib.CategoryTheory.Monoidal.Functor
import all WeilConjectures.CategoryTheory.FlatPairingPullbackAssembly
import all WeilConjectures.AlgebraicGeometry.OrdinaryFiniteTwistTransportUniqueness
import all Mathlib.CategoryTheory.Adjunction.Whiskering
import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1EvaluationRecipeBaseChange

/-! # The two ordinary projective-line components commute with arbitrary base change
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true

universe u

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

attribute [local implicit_reducible] ordinaryFiniteSingleFunctor ordinaryFiniteDegreeZero

attribute [local irreducible] singleFunctorPullbackMap
  upperStar Functor.leftDerivedFunctor
  Functor.rightDerivedFunctor Functor.mapDerivedCategory

attribute [local irreducible] AlgebraicGeometry.ProjectiveSpace
  HasDerivedCategory.ofIsGrothendieckAbelian DerivedCategory.singleFunctors

private theorem adjunct_square_core
    {C D E F : Type*} [Category C] [Category D] [Category E] [Category F]
    {L : C ⥤ D} {R : D ⥤ C} {L' : E ⥤ F} {R' : F ⥤ E}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (G : C ⥤ E) (H : D ⥤ F)
    (θ : TwoSquare G L L' H) {P : C} {P' : E} {K : D} {K' : F}
    (z : L.obj P ⟶ K) (z' : L'.obj P' ⟶ K') (b : G.obj P ⟶ P')
    (d : H.obj K ⟶ K')
    (hz : θ.app P ≫ H.map z ≫ d = L'.map b ≫ z') :
    G.map (adj.homEquiv _ _ z) ≫ (mateEquiv adj adj' θ).app K ≫ R'.map d =
      b ≫ adj'.homEquiv _ _ z' := by
  rw [reassoc_of% adjunct_mate adj adj' G H θ z]
  rw [← adj'.homEquiv_naturality_right, ← adj'.homEquiv_naturality_left]
  apply congrArg (adj'.homEquiv _ _)
  simpa only [Category.assoc] using hz

private theorem native_general_adjunct_square (A : Type (u + 1)) [CommRing A]
    {X X' Y Y' : Scheme.{u}} {q : X ⟶ Y} {q' : X' ⟶ Y'}
    {g : X' ⟶ X} {f : Y' ⟶ Y} (sq : CommSq g q' q f)
    {P : DerivedCategoryModule A Y} {P' : DerivedCategoryModule A Y'}
    {K : DerivedCategoryModule A X} {K' : DerivedCategoryModule A X'}
    (z : (ordinaryFinitePullback A q).obj P ⟶ K)
    (z' : (ordinaryFinitePullback A q').obj P' ⟶ K')
    (b : (ordinaryFinitePullback A f).obj P ⟶ P')
    (d : (ordinaryFinitePullback A g).obj K ⟶ K')
    (hz : (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom.app P ≫
      (ordinaryFinitePullback A g).map z ≫ d = (ordinaryFinitePullback A q').map b ≫ z') :
    (ordinaryFinitePullback A f).map
        ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q).homEquiv _ _ z) ≫
      (derivedBaseChangeMap (ModuleCat.{u + 1} A) sq).app K ≫
        (ordinaryFinitePushforward A q').map d =
      b ≫ (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q').homEquiv _ _ z' := by
  dsimp only [derivedBaseChangeMap, derivedBaseChangeSquare, ordinaryFinitePushforward,
    ordinaryFinitePullback]
  exact adjunct_square_core
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q)
    (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) q')
    (ordinaryFinitePullback A f) (ordinaryFinitePullback A g)
    (TwoSquare.mk _ _ _ _ (derivedSquareUpperStarIso (ModuleCat.{u + 1} A) sq).hom)
    z z' b d hz

/-- The actual scalar Kummer class pulls back to the actual scalar Kummer class,
and its evaluation adjunct, as well as the constant unit, commutes with exchange.
This is a statement about the two components, with no splitting or invertibility
assertion and no Noetherian assumption. -/
theorem ordinaryFiniteP1_components_baseChange
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : ℕ) (hN : 0 < N) (hA : (N : A) = 0)
    {S' S : Scheme.{u}} (g : S' ⟶ S) (hS : IsUnit (N : Γ(S, ⊤)))
    (hS' : IsUnit (N : Γ(S', ⊤)))
    (c : ordinaryFiniteUnit A (ProjectiveLine S) ⟶
      (ordinaryFiniteLine A N hA (ProjectiveLine S))⟦(2 : ℤ)⟧)
    (hc : ordinaryFiniteP1ChernSpec A N hA S
      ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
        hS.map (ProjectiveLine S ↘ S).appTop.hom) c) :
    ∃ c' : ordinaryFiniteUnit A (ProjectiveLine S') ⟶
        (ordinaryFiniteLine A N hA (ProjectiveLine S'))⟦(2 : ℤ)⟧,
      ordinaryFiniteP1ChernSpec A N hA S'
        ((map_natCast (ProjectiveLine S' ↘ S').appTop.hom N) ▸
          hS'.map (ProjectiveLine S' ↘ S').appTop.hom) c' ∧
      ((ordinaryFinitePullback A g).map (p1DecompositionUnit A S) ≫
        ordinaryFiniteP1Exchange A g (ordinaryFiniteUnit A (ProjectiveLine S)) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteUnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom =
        (ordinaryFiniteUnitPullback A g).hom ≫ p1DecompositionUnit A S') ∧
      ((ordinaryFinitePullback A g).map (p1DecompositionChernAdjoint A N hN hA S hS c) ≫
        ordinaryFiniteP1Exchange A g (ordinaryFiniteUnit A (ProjectiveLine S)) ≫
        (ordinaryFinitePushforward A (ProjectiveLine S' ↘ S')).map
          (ordinaryFiniteUnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom =
        (p1DecompositionTwistPullback A N hN hA g hS (-1) (-2)).hom ≫
          p1DecompositionChernAdjoint A N hN hA S' hS' c') := by
  let hP' : IsUnit (N : Γ(ProjectiveLine S', ⊤)) :=
    (map_natCast (ProjectiveLine S' ↘ S').appTop.hom N) ▸
      hS'.map (ProjectiveLine S' ↘ S').appTop.hom
  obtain ⟨c', hc'⟩ := (ordinaryFiniteClass_bijective_arbitraryBase A (ProjectiveLine S')
    (Scheme.finiteEtaleTateLine (ProjectiveLine S') N A hA) 2).2
      (ordinaryFiniteP1KummerClass A N hA S' hP')
  have hc'spec : ordinaryFiniteP1ChernSpec A N hA S' hP' c' := hc'
  refine ⟨c', hc'spec, ?_, ?_⟩
  · unfold p1DecompositionUnit
    rw [line_projective_exchange]
    have h := native_adjunct_square A
      (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq
      (𝟙 (ordinaryFiniteUnit A (ProjectiveLine S)))
      (𝟙 (ordinaryFiniteUnit A (ProjectiveLine S')))
      (ordinaryFiniteUnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom
      (by simp)
    simpa only [Category.comp_id] using h
  · have hcmap := ordinaryFiniteP1_chern_map_baseChange A N hN hA
      (positive_transport A N hN hA) g hS hS' c c' hc hc'spec
    have hz := ordinaryFiniteP1_evaluationRecipe_baseChange A N hN hA
      (positive_transport A N hN hA)
      (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq hS hS'
      ((map_natCast (ProjectiveLine S ↘ S).appTop.hom N) ▸
        hS.map (ProjectiveLine S ↘ S).appTop.hom) hP' c c' hcmap
    unfold p1DecompositionChernAdjoint
    rw [p1DecompositionTensorAdjoint, p1DecompositionTensorAdjoint, line_projective_exchange]
    exact native_general_adjunct_square A
      (ProjectiveSpace.isPullback_map (ULift.{u} (Fin 2)) g).toCommSq _ _
      (p1DecompositionTwistPullback A N hN hA g hS (-1) (-2)).hom
      (ordinaryFiniteUnitPullback A (ProjectiveSpace.map (ULift.{u} (Fin 2)) g)).hom hz

end AlgebraicGeometry.Etale
