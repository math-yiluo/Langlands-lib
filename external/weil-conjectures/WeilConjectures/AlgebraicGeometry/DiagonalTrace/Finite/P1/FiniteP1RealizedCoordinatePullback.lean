/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1OrdinaryCoordinateArrows
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteChernPullback
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
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
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
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
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryPullbackComparison

/-! # Pullback of arbitrary ordinary arrows in the finite coordinates

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-p1-realized-coordinate-pullback).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
set_option linter.auxLemma false in
-- Reuse the sheafification and localization witnesses stored in the endpoint maps.
attribute [local instance 100000] finiteKummerUnitCoordinate._proof_4
  finiteKummerUnitCoordinate._proof_5 finiteKummerUnitCoordinate._proof_9
  finiteKummerUnitCoordinate._proof_10
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
open SpTowerClasses
attribute [local instance 100000] CategoryTheory.Abelian.toPreadditive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [local instance 100000] Etale.ordinaryFiniteDerivedCategoryInstance
attribute [local implicit_reducible] Etale.ordinaryFiniteDerivedCategoryInstance
  Etale.ordinaryFiniteSingleFunctor Etale.ordinaryFiniteDegreeZero
attribute [local irreducible] Functor.mapDerivedCategory SpTowerP1.nuSingle
  HasDerivedCategory.ofIsGrothendieckAbelian HomologicalComplex.quasiIso
  Etale.projectiveLineTraceTransport
  geoP1PullComparison
  Etale.ordinaryFiniteUnitPullback Etale.ordinaryFiniteShiftedLinePullback

private theorem realized_normalized_arrow
    {C D H : Type*} [Category C] [Category D] [Category H]
    (R : D ⥤ H) (G : C ⥤ D) {U V : D} {U' V' : C} {A A₀ B B₀ : H}
    (u : U ≅ G.obj U') (v : V ≅ G.obj V')
    (S₁ : A ≅ A₀) (S₂ : A₀ ≅ R.obj (G.obj U'))
    (T₁ : R.obj (G.obj V') ≅ B₀) (T₂ : B₀ ≅ B)
    (a : U ⟶ V) (b : U' ⟶ V')
    (h : u.inv ≫ a ≫ v.hom = G.map b) :
    (S₁ ≪≫ S₂ ≪≫ R.mapIso u.symm).hom ≫ R.map a ≫
        (T₂.symm ≪≫ T₁.symm ≪≫ R.mapIso v.symm).inv =
      (S₁ ≪≫ S₂).hom ≫ R.map (G.map b) ≫ (T₁ ≪≫ T₂).hom := by
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
    Functor.mapIso_hom, Functor.mapIso_inv, Category.assoc]
  simpa only [Functor.map_comp, Category.assoc] using
    congrArg (fun f ↦ S₁.hom ≫ S₂.hom ≫ R.map f ≫ T₁.hom ≫ T₂.hom) h

/-- Intrinsic realization of the normalized ordinary pullback square.
Source: diagonal-tower trace (1), exact comparison and pullback
(blueprint: lem-sfb-finite-p1-realized-coordinate-pullback).

Proof: use finiteOrdinaryPullback_comparison, then apply intrinsic realization.
The generic realized_normalized_arrow formula composes this square with the
actual single and coordinate isomorphisms. Expand only the two specified
projective-line endpoint coordinates and associate their isomorphisms. -/
theorem finiteP1_realized_coordinate_pullback (n : ℕ)
    [Finite (SpTowerShriek.R l E n)] {X S : Scheme.{u}}
    (e : X ≅ ProjectiveLine S) (hS : IsUnit (l : Γ(S, ⊤)))
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX)
    (a : Etale.ordinaryFiniteUnit (FiniteRing l E n) (ProjectiveLine S) ⟶
      (Etale.ordinaryFiniteLine (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext (coefficient_annihilates l E n)) (ProjectiveLine S))⟦(2 : ℤ)⟧) :
    @Eq (finiteKummerUnit l E X n ⟶ finiteKummerLine l E X n)
      (finiteP1CoordinateImage l E n e hS c a)
      (finiteP1LocalCoordinateImage l E n X c
        (Etale.ordinaryFiniteLinePullbackMap (FiniteRing l E n) (l ^ (n + 1))
          (ULift.ext (coefficient_annihilates l E n))
          (Etale.projectiveLineTraceTransport (l ^ (n + 1))
            (pow_pos (Fact.out : l.Prime).pos _) (FiniteRing l E n)
            (ULift.ext (coefficient_annihilates l E n))) e.hom
          (finiteP1_unitOnPullback (l ^ (n + 1)) (ProjectiveLine S ↘ S)
            (by simpa only [Nat.cast_pow] using hS.pow (n + 1))) a)) := by
  exact realized_normalized_arrow (A := finiteKummerUnit l E X n)
    (B := finiteKummerLine l E X n)
    (Scheme.sfIntrinsicModuleEquivalence X
      (SpTowerShriek.R l E n)).functor.mapDerivedCategory
    (geoP1Comparison (FiniteRing l E n) X)
    (geoP1UnitPullback (FiniteRing l E n) e.hom)
    (geoP1TwistPullback (FiniteRing l E n) (l ^ (n + 1))
      (pow_pos (Fact.out : l.Prime).pos _)
      (ULift.ext (coefficient_annihilates l E n)) e.hom
      (finiteP1_unitOnPullback (l ^ (n + 1)) (ProjectiveLine S ↘ S)
        (by simpa only [Nat.cast_pow] using hS.pow (n + 1))) 1 2)
    (((DerivedCategory.singleFunctor _ 0).mapIso c.unit).symm)
    ((SpTowerP1.nuSingle l E n X _).symm)
    (((SpTowerP1.nu l E n X).commShiftIso (2 : ℤ)).app _)
    ((shiftFunctor _ (2 : ℤ)).mapIso
      ((SpTowerP1.nuSingle l E n X _) ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso c.line))
    ((geoP1Pullback (FiniteRing l E n) e.hom).map
      ((geoP1Comparison (FiniteRing l E n) (ProjectiveLine S)).map a))
    (Etale.ordinaryFiniteLinePullbackMap (FiniteRing l E n) (l ^ (n + 1))
      (ULift.ext (coefficient_annihilates l E n))
      (Etale.projectiveLineTraceTransport (l ^ (n + 1))
        (pow_pos (Fact.out : l.Prime).pos _) (FiniteRing l E n)
        (ULift.ext (coefficient_annihilates l E n))) e.hom
      (finiteP1_unitOnPullback (l ^ (n + 1)) (ProjectiveLine S ↘ S)
        (by simpa only [Nat.cast_pow] using hS.pow (n + 1))) a)
    (finiteOrdinaryPullback_comparison (FiniteRing l E n) (l ^ (n + 1))
      (pow_pos (Fact.out : l.Prime).pos _)
      (ULift.ext (coefficient_annihilates l E n)) e.hom
      (finiteP1_unitOnPullback (l ^ (n + 1)) (ProjectiveLine S ↘ S)
        (by simpa only [Nat.cast_pow] using hS.pow (n + 1))) a)

end AlgebraicGeometry.ProEtale.DiagonalTrace
