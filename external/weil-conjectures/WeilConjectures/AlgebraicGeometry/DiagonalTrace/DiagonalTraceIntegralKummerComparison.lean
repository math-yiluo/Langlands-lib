/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.DiagonalTraceIntegralKummerClass
public import WeilConjectures.CategoryTheory.Abelian.Ext.MapExactFunctorConj
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteFirstChern
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinaryFiniteP1KummerSupplement
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteClassArbitraryBase
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerBoundaryComparison
public import WeilConjectures.AlgebraicGeometry.EtaleModuleInjectiveForgetAcyclic
public import WeilConjectures.CategoryTheory.Sites.SheafCohomologyRightDerived
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteP1Arrows
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
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteChernPullback
public import WeilConjectures.AlgebraicGeometry.OrdinaryFiniteCoefficientRecords
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
public import WeilConjectures.AlgebraicGeometry.FiniteP1ChernMapBaseChange
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicardPullback
public import WeilConjectures.AlgebraicGeometry.SupportedDerivedUnitForget
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerSystemSupplement
public import WeilConjectures.ConstructibleSheaf.FinitePushforward.ConstantUnit
public import WeilConjectures.CategoryTheory.DerivedSingleUnitExact
public import WeilConjectures.CategoryTheory.DerivedSingleUnit
public import WeilConjectures.CategoryTheory.DerivedCategory.Adjunction
import all WeilConjectures.AlgebraicGeometry.Cartier.CartierReductionSiteComparison
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-! # The two-site comparison of the positive integral Kummer composite -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option synthInstance.maxSize 4096
attribute [local instance 3000] CategoryTheory.CategoryStruct.toQuiver
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses
attribute [local irreducible] DerivedCategory Functor.mapDerivedCategory
  CategoryTheory.Abelian.Ext comparisonUpperStar cartierProRootMap
  Ext.homEquiv Ext.comp Ext.mk₀ Ext.mk₀CompMk₀ Ext.mapExactFunctor
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits
attribute [local implicit_reducible] powerUnits constant Functor.ofOpSequence
  Functor.ofSequence Scheme.proEtaleRootsOfUnityTower

private theorem mapSingleArrow_ext {C D : Type*} [Category C] [Category D]
    [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [HasExt C] [HasExt D] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : C} (n : ℕ) (β : Ext X Y n) :
    (β.mapExactFunctor F).hom = mapSingleArrow F (n : ℤ) β.hom := by
  simp only [Ext.mapExactFunctor_hom, ShiftedHom.map, mapSingleArrow, Category.assoc]
private theorem mapSingleArrow_id {C : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [HasExt C] [EnoughInjectives C]
    {X Y : C} (n : ℕ)
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) :
    mapSingleArrow (𝟭 C) (n : ℤ) f = f := by
  let β : Ext X Y n := Ext.homEquiv.symm f
  have hβ : β.hom = f := Ext.homEquiv.apply_symm_apply f
  rw [← hβ, ← mapSingleArrow_ext, Ext.mapExactFunctor_id]
  rfl

-- Stating the source as `Ab T` (as `lineBundleClass` does) keeps the kernel from unfolding
-- both sides of `Quiver.Hom` to reconcile `Ab T` with its unfolding.
private theorem mapSingleArrow_constant_evaluation (T : Scheme.{u}) (n : ℕ) {X Y : DiagonalAb T}
    (f : (DerivedCategory.singleFunctor (DiagonalAb T) 0).obj X ⟶
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).obj Y)⟦(1 : ℤ)⟧) :
    mapSingleArrow (C := Ab T) (abEvaluation T n) (1 : ℤ)
      (mapSingleArrow (constant T) (1 : ℤ) f) = f := by
  rw [mapSingleArrow_composite]
  exact mapSingleArrow_id 1 f

private theorem evaluatedLineBundleArrow (T : Scheme.{u}) (P : T.Pic) (n : ℕ) :
    mapSingleArrow (C := Ab T) (abEvaluation T n) (1 : ℤ) (lineBundleClass T P) =
      lineBundleEtaleClass T P :=
  mapSingleArrow_constant_evaluation T n (lineBundleEtaleClass T P)
private theorem extClass_heq {C : Type*} [Category C] [Abelian C] [HasExt C]
    {S₁ S₂ : ShortComplex C} (h : S₁ = S₂)
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) : HEq h₁.extClass h₂.extClass := by
  cases h
  rfl

-- Compare the actual tower and finite Kummer short-complex presentations.
private theorem evaluatedKummerExt (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (k : Kummer l T) (n : ℕ) (hn : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))) :
    k.exact.extClass.mapExactFunctor (C := Ab T) (abEvaluation T n) =
      (cartierProKummer_exact T (l ^ (n + 1))
        (pow_pos (Fact.out : l.Prime).pos _) hn).extClass := by
  have hs : (ShortComplex.mk k.inclusion k.power k.zero).map (abEvaluation T n) =
      cartierProKummerComplex T (l ^ (n + 1)) := by
    change ShortComplex.mk (k.inclusion.app (op n)) (k.power.app (op n)) _ =
      ShortComplex.mk (Scheme.proEtaleRootsOfUnityInclusion T (l ^ (n + 1)))
        (Scheme.proEtaleUnitsPower T (l ^ (n + 1))) _
    congr 1
    · exact k.inclusion_eq n
    · exact k.power_eq n
  rw [Ext.mapExactFunctor_extClass]
  exact eq_of_heq (extClass_heq hs _ _)
private theorem mapSingleArrow_inverseExt
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D] [HasExt C] [HasExt D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {X Y : C} (n : ℕ)
    (f : (DerivedCategory.singleFunctor C 0).obj X ⟶
      ((DerivedCategory.singleFunctor C 0).obj Y)⟦(n : ℤ)⟧) :
    ((Ext.homEquiv.symm f).mapExactFunctor F).hom = mapSingleArrow F (n : ℤ) f := by
  rw [mapSingleArrow_ext]
  exact congrArg (mapSingleArrow F (n : ℤ)) (Ext.homEquiv.apply_symm_apply f)

private theorem extEndpointsHom
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C] [HasExt C]
    {X' X Y Y' : C} (a : X' ⟶ X) (n : ℕ) (β : Ext X Y n) (b : Y ⟶ Y') :
    (Ext.mk₀CompMk₀ a β b).hom =
      (DerivedCategory.singleFunctor C 0).map a ≫ β.hom ≫
        ((DerivedCategory.singleFunctor C 0).map b)⟦(n : ℤ)⟧' := by
  simp only [Ext.mk₀CompMk₀, Ext.comp_hom, Ext.mk₀_hom,
    ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀]

private theorem evaluatedLineBundleExt (T : Scheme.{u}) (P : T.Pic) (n : ℕ) :
    (Ext.homEquiv.symm (lineBundleClass T P)).mapExactFunctor (C := Ab T) (abEvaluation T n) =
      Ext.mk₀CompMk₀ (integerComparison T).inv
        ((Scheme.Pic.toCohomologicalPicardGroup T P).mapExactFunctor
          (comparisonUpperStar AddCommGrpCat.{u + 1} T))
        (cartierUnitsComparison T) := by
  apply Ext.ext
  rw [mapSingleArrow_inverseExt]
  simp only [Int.natCast_one]
  rw [evaluatedLineBundleArrow, extEndpointsHom, mapSingleArrow_ext]
  rfl

private theorem ordinaryKummer_comp (A : Type (u + 1)) [CommRing A]
    (N : ℕ) (hA : (N : A) = 0) (T : Scheme.{u})
    (hT : IsUnit (N : Γ(T, ⊤))) (P : T.Pic) :
    Etale.ordinaryFiniteKummerClass A N hA T hT P =
      (Scheme.Pic.toCohomologicalPicardGroup T P).comp
        (cartierEtaleKummerUnit A N hA T hT) (rfl : 1 + 1 = 2) := by
  change ((Scheme.Pic.toCohomologicalPicardGroup T P).comp
    (T.kummerSequence_shortExact N hT).extClass (rfl : 1 + 1 = 2)).comp
      (Ext.mk₀ (Etale.ordinaryFiniteRootMap A N hA T)) (add_zero 2) =
    (Scheme.Pic.toCohomologicalPicardGroup T P).comp
      ((T.kummerSequence_shortExact N hT).extClass.comp
        (Ext.mk₀ (Etale.ordinaryFiniteRootMap A N hA T)) (add_zero 1)) (rfl : 1 + 1 = 2)
  exact Ext.comp_assoc _ _ _ _ _ rfl

/-- The evaluated integral Kummer composite is the comparison image of the
ordinary etale Kummer class. This assertion has no Chern data, scalar restriction,
frame, supplied finite lift, support, or limiting arrow.

Source: geometric tower classes proof (2), positive Kummer connecting map;
Cartier reduction site comparison, Kummer comparison paragraph; Stacks 03PL.
(blueprint: lem-sfb-diagonal-trace-integral-kummer-comparison).

Proof: represent lineBundleClass as an Ext class and evaluate the Yoneda
composite. Exact functors preserve Yoneda composition. Evaluation composed with
the constant tower functor is identity, so the evaluated line-bundle extension
is the etale Picard extension mapped through comparison, with integerComparison
and cartierUnitsComparison at its ends. Compare the evaluated short complex of
k with cartierProKummerComplex using inclusion_eq and power_eq; naturality of
extension classes identifies their connecting classes. Compose with the root
map and apply kummer_comparison: the pro-etale Kummer unit is the comparison
image of the ordinary etale Kummer unit. Ext associativity moves the integral
source comparison outside and gives Pic(P) composed with that etale unit.
Sheaf.H.map_apply and Sheaf.H.δSucc_apply identify this composite with
ordinaryFiniteKummerClass. The target comparison equals forgetComparisonIso.hom
by its adjunction-mate formula. Positive n+1 covers n=0; the same functorial
calculation covers zero coefficient rings, trivial P and the empty scheme. -/
theorem diagonalTrace_integralKummer_comparison
    (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (A : Type (u + 1)) [CommRing A] (n : ℕ)
    (hA : ((l ^ (n + 1) : ℕ) : A) = 0) (k : Kummer l T)
    (hN : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))) (P : T.Pic) :
    evaluatedIntegralKummerClass l T A n hA k hN P =
    Ext.mk₀CompMk₀ (integerComparison T).inv
      ((Etale.ordinaryFiniteKummerClass A (l ^ (n + 1)) hA T hN P).mapExactFunctor
        (comparisonUpperStar AddCommGrpCat.{u + 1} T))
      ((forgetComparisonIso A T).hom.app (Scheme.finiteEtaleTateLine T
        (l ^ (n + 1)) A hA)) := by
  have hK := kummer_comparison A (l ^ (n + 1)) hA T
    (pow_pos (Fact.out : l.Prime).pos _) hN
  simp only [cartierProKummerUnit, cartierKummerClass, cartierForgetComparison] at hK
  unfold evaluatedIntegralKummerClass
  rw [Ext.mapExactFunctor_comp, evaluatedLineBundleExt, evaluatedKummerExt l T k n hN,
    ordinaryKummer_comp, Ext.mapExactFunctor_comp]
  simp only [Ext.mk₀CompMk₀, Ext.comp_assoc, forgetComparisonIso_hom]
  rw [hK]
  rfl

end AlgebraicGeometry.ProEtale.DiagonalTrace
