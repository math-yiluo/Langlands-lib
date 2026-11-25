/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalization
public import WeilConjectures.AlgebraicGeometry.Etale.Sum.EtaleSumExtensionTensor
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
import WeilConjectures.AlgebraicGeometry.SfEtaleGraphProjectionArbitraryBase
import WeilConjectures.AlgebraicGeometry.SfEtaleAmbientAdjointProjection
import WeilConjectures.AlgebraicGeometry.DerivedCategories
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjection
import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.AlgebraicGeometry.EtaleProperDerivedDirectImageAdjoint
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRightAdjoint
import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownCohomologicalRepresentability
import Mathlib.CategoryTheory.Triangulated.Yoneda
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetract
import Mathlib.CategoryTheory.Retract
import Mathlib.CategoryTheory.Adjunction.FullyFaithful
import WeilConjectures.CategoryTheory.GrothendieckDerivedBrownRetractData
import Mathlib.CategoryTheory.Adjunction.Basic
import WeilConjectures.CategoryTheory.GrothendieckDerivedCompactLocalizationModel
import WeilConjectures.CategoryTheory.CompactlyGenerated
import Mathlib.CategoryTheory.Triangulated.Functor
import WeilConjectures.CategoryTheory.GrothendieckDerivedGabrielPopescuPresentation
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.CategoryTheory.Equivalence
import WeilConjectures.CategoryTheory.GabrielPopescuAbelianCore
import WeilConjectures.CategoryTheory.GabrielPopescuLargeHomRightAdjoint
import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.CategoryTheory.Preadditive.Yoneda.Limits
import WeilConjectures.CategoryTheory.DerivedLargeCoproductsTransfer
import WeilConjectures.CategoryTheory.DerivedHomologyInjective
import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import Mathlib.CategoryTheory.Preadditive.Injective.Basic
import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveSurjective
import Mathlib.Algebra.Homology.SingleHomology
import WeilConjectures.CategoryTheory.DerivedHomologyInjectiveInjective
import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
import WeilConjectures.CategoryTheory.LargeHomSolutionSet
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.ModuleEmbedding.GabrielPopescu
import Mathlib.Algebra.Category.ModuleCat.AB
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import WeilConjectures.CategoryTheory.CompactDerivedSourceCore
import WeilConjectures.CategoryTheory.DerivedModuleCompactGeneration
import Mathlib.Algebra.Homology.DerivedCategory.Basic
import WeilConjectures.CategoryTheory.DerivedModuleRankOneProperties
import Mathlib.Algebra.Module.ULift
import WeilConjectures.CategoryTheory.CompactObject
import WeilConjectures.CategoryTheory.WeakTriangulatedGenerator
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompact
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactInjective
import WeilConjectures.CategoryTheory.DerivedModuleRankOneCompactSurjective
import WeilConjectures.CategoryTheory.DerivedModuleDirectSums
import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Category.ModuleCat.Products
import WeilConjectures.CategoryTheory.DerivedModuleRankOneGenerator
import WeilConjectures.CategoryTheory.DerivedModuleRankOneNonzeroMap
import WeilConjectures.CategoryTheory.DerivedModuleNonzeroClassMap
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
import WeilConjectures.CategoryTheory.TriangulatedEquivalenceTransfer
import WeilConjectures.CategoryTheory.CompactGenerationEquivalence
import Mathlib.CategoryTheory.Category.ULift
import Mathlib.CategoryTheory.Adjunction.Limits
import WeilConjectures.CategoryTheory.GrothendieckDerivedExactLocalization
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import Mathlib.CategoryTheory.Adjunction.Additive
import WeilConjectures.CategoryTheory.BrownCohomologicalRepresentabilityUniverseTransfer
import Mathlib.CategoryTheory.Limits.Preserves.Opposites
import Mathlib.CategoryTheory.Triangulated.Opposite.Functor
import WeilConjectures.CategoryTheory.SmoothPurity.CountableCoproductsIdempotentComplete
import Mathlib.CategoryTheory.Adjunction.PartialAdjoint
import WeilConjectures.CategoryTheory.GrothendieckDerivedCoproducts
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.CategoryTheory.ProjectionFormulaCoproducts
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
import WeilConjectures.CategoryTheory.CoproductsOfCopowers
import Mathlib.CategoryTheory.MorphismProperty.Retract
import WeilConjectures.SixFunctors.Etale.Derived.ProjectionFormula
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriek
import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactification
import WeilConjectures.AlgebraicGeometry.ExactPullbackTensorComparison
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comparison
import WeilConjectures.AlgebraicGeometry.SfEtaleGraphUnitTensor
import WeilConjectures.AlgebraicGeometry.SfEtaleGraphExchangeTensor
import WeilConjectures.AlgebraicGeometry.SfEtaleGraphTransferTensor
import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
import WeilConjectures.CategoryTheory.Adjunction.ProjectionMapCompat
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal.Comp
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekCompactificationIso
import all WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange
import all WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
import all WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import all WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import all WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekBaseChange
import all WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube
import all WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import all WeilConjectures.AlgebraicGeometry.Unbounded.UnboundedProperOpenCompositionSupplement

/-! Core mate equation for compact-support graph tensor evaluation.
(blueprint: lem-pur-compact-support-graph-tensor-evaluation-core).

Proof: evaluate the normalized graph comparison on local tensor generators, where the unit
equation determines the sum-extension tensor mate. The graph and complementary restrictions
agree sectionwise. Pass to flat-term K-flat representatives, totalize degreewise, and use the
canonical tensor, open projection, and compactification comparisons. Derived localization
descent then gives the unbounded mate equation. -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale
attribute [local instance 2000] Sheaf.instHasColimitsOfShape
attribute [local irreducible] Functor.mapDerivedCategory Adjunction.mapDerivedCategoryAdjunction
  derivedUpperStarLowerStarAdjunction leftDerivedUpperStarIsoMapDerivedCategory
  etaleLowerShriek upperStar lowerStar openImmersionLowerShriek derivedTensor
  Functor.leftDerivedFunctor Functor.rightDerivedFunctor

private theorem graphComparison_eq_source
    (A : Type (u + 1)) [CommRing A] [Finite A]
    {V T : Scheme.{u}} (e : V ⟶ T) [Etale e] [IsSeparated e]
    (c : Compactification e) :
    GraphExchange.compactificationEtaleComparison (ModuleCat.{u + 1} A) e c =
      compactificationEtaleComparison A e c := by
  have hb : GraphExchange.clopenUpperStarLowerShriekAdjunction
      (ModuleCat.{u + 1} A) c.graphExchangeSection =
        clopenUpperStarLowerShriekAdjunction A c.selfGraph := by
    apply Adjunction.ext_counit
    ext J
    rw [GraphExchange.clopenUpperStarLowerShriekAdjunction_counit_app,
      clopenUpperStarLowerShriekAdjunction_counit_app]
    rfl
  have hG : GraphExchange.compactificationEtaleGraphIso (ModuleCat.{u + 1} A) e c =
      compactificationEtaleGraphIso A e c := by
    unfold GraphExchange.compactificationEtaleGraphIso graph_iso_from_units
      compactificationEtaleGraphIso
    rfl
  have hg : GraphExchange.compactificationEtaleGraphMap (ModuleCat.{u + 1} A) e c =
      compactificationEtaleGraphMap A e c := by
    ext J
    rw [GraphExchange.compactificationEtaleGraphMap_app]
    dsimp only [GraphExchange.clopenTransfer, compactificationEtaleGraphMap, clopenTransfer]
    rw [hb, hG]
    rfl
  have hu : GraphExchange.compactificationEtaleUnit (ModuleCat.{u + 1} A) e c =
      compactificationEtaleUnit A e c := by
    unfold GraphExchange.compactificationEtaleUnit graph_unit_from_exchange
      compactificationEtaleUnit
    rw [hg]
  unfold GraphExchange.compactificationEtaleComparison transpose_natTrans
    compactificationEtaleComparison
  rw [hu]

private theorem normalizedComparison_eq_source
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
    [IsLocallyNoetherian T] [CompactSpace T]
    (e : V ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e) :
    (N.comparison e c).inv = compactificationEtaleComparison A e c := by
  have ha : N.sheafComparison e c = etaleCompactificationGraphMap A e c := by
    apply NatTrans.ext
    funext J
    have : Mono ((openImmersionLowerShriekToLowerStar
        (ModuleCat.{u + 1} A) c.i).app J) := open_compare_mono A c.i J
    have : Mono ((compactificationSheafToDirectImage A c).app J) := by
      dsimp only [compactificationSheafToDirectImage, NatTrans.comp_app,
        Functor.whiskerRight_app]
      have : Mono ((lowerStar (ModuleCat.{u + 1} A) c.g).map
        ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app J)) :=
          Functor.map_mono _ _
      exact mono_comp
        ((lowerStar (ModuleCat.{u + 1} A) c.g).map
          ((openImmersionLowerShriekToLowerStar (ModuleCat.{u + 1} A) c.i).app J))
        ((lowerStarComp.{u + 2, u} (ModuleCat.{u + 1} A) c.i c.g e c.comm).app J).hom
    apply (cancel_mono ((compactificationSheafToDirectImage A c).app J)).1
    exact (N.sheaf_normalization e c J).trans
      (compactSupportGraphSheafComparison_normalization A e c J).symm
  calc
    _ = compactSupportDerivedComparison A e c (N.sheafComparison e c) := by
      apply Localization.natTrans_ext DerivedCategory.Qh
        (HomotopyCategory.quasiIso (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A))
          (.up ℤ))
      intro H
      exact (N.derived_normalization e c H).trans
        (compactSupportDerivedComparison_app A e c (N.sheafComparison e c) H).symm
    _ = _ := by rw [ha, GraphExchange.graph_comparison_eq, graphComparison_eq_source]

private theorem tensorComparison_eq
    (A : Type (u + 1)) [CommRing A] {V T : Scheme.{u}} (e : V ⟶ T)
    (B K : DerivedCategoryModule A T) :
    (etaleSumExtensionTensorPullbackIso A e B K).hom =
      (sfEtaleExactPullbackTensorIso A e B K).inv := by
  simp only [etaleSumExtensionTensorPullbackIso, sfEtaleExactPullbackTensorIso,
    supportExactPullbackTensorIso, supportDerivedTensorIso, Iso.trans_inv, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, Category.assoc]
  rw [NatTrans.naturality_assoc]

-- Keep the statement's original unused `adj` let binding verbatim.
set_option linter.unusedVariables false in
/-- The normalized comparison satisfies the mate equation before transposing through the
compactification adjunction. This is the core tensor calculation; the graph evaluation theorem
is obtained by applying the adjunction hom-equivalence. Source: Stacks Tags 0GKF and 0GL5.
(blueprint: lem-pur-compact-support-graph-tensor-evaluation-core).

Proof: evaluate the normalized graph comparison on local tensor generators, where the unit
equation determines the sum-extension tensor mate. The graph and complementary restrictions
agree sectionwise. Pass to flat-term K-flat representatives, totalize degreewise, and use the
canonical tensor, open projection, and compactification comparisons. Derived localization
descent then gives the unbounded mate equation. -/
theorem compactSupportGraph_tensor_evaluation_core
    (A : Type (u + 1)) [CommRing A] [Finite A]
    (N : EtaleCompactSupportNormalization A)
    {V T : Scheme.{u}} [IsLocallyNoetherian V] [CompactSpace V]
    [IsLocallyNoetherian T] [CompactSpace T]
    (e : V ⟶ T) [Etale e] [IsSeparated e]
    [LocallyOfFiniteType e] [QuasiCompact e] (c : Compactification e)
    (M : DerivedCategory (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} A)))
    (K : DerivedCategory (Sheaf T.smallEtaleTopology (ModuleCat.{u + 1} A))) :
    let S : DerivedCategoryModule A V ⥤ DerivedCategoryModule A T :=
      (etaleLowerShriek (ModuleCat.{u + 1} A) e inferInstance).mapDerivedCategory
    let E : DerivedCategoryModule A T ⥤ DerivedCategoryModule A V :=
      (upperStar (ModuleCat.{u + 1} A) e).mapDerivedCategory
    let T₀ := derivedTensor (ModuleCat.{u + 1} A) T
    let V₀ := derivedTensor (ModuleCat.{u + 1} A) V
    let adj := derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} A) c.g
    ∀ q : S.obj ((V₀.obj M).obj (E.obj K)) ⟶ (T₀.obj (S.obj M)).obj K,
      ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
        inferInstance).mapDerivedCategoryAdjunction).unit.app _ ≫ E.map q =
        (V₀.map ((etaleLowerShriekUpperStarAdjunction (ModuleCat.{u + 1} A) e
          inferInstance).mapDerivedCategoryAdjunction.unit.app M)).app (E.obj K) ≫
          (etaleSumExtensionTensorPullbackIso A e (S.obj M) K).hom →
      q ≫ (T₀.map ((N.comparison e c).inv.app M)).app K ≫
          ((projectionMapOfCompactification (ModuleCat.{u + 1} A) c).app M).app K ≫
          (rightDerivedLowerShriekOfCompactification (ModuleCat.{u + 1} A) c).map
            ((V₀.obj M).map
              ((leftDerivedUpperStarIsoMapDerivedCategory
                (ModuleCat.{u + 1} A) e).hom.app K)) =
        (N.comparison e c).inv.app ((V₀.obj M).obj (E.obj K)) := by
  dsimp only
  intro q hq
  -- The normalization fixes the sheaf map, then its unique derived descent.
  have ht := normalizedComparison_eq_source A N e c
  have hq' : q = sfEtaleSumExactTensorMap A e M K := by
    apply ((derivedEtaleLowerShriekMapAdjunction
      (ModuleCat.{u + 1} A) e).homEquiv _ _).injective
    simpa only [sfEtaleSumExactTensorMap, Equiv.apply_symm_apply,
      Adjunction.homEquiv_unit, derivedEtaleLowerShriekMapAdjunction,
      tensorComparison_eq] using hq
  rw [ht, hq']
  -- The existing graph theorem gives the inverse-projection form of the same square.
  have h := (sfEtaleGraphProjectionArbitraryBase A e c).2 M K
  change sfEtaleSumExactTensorMap A e M K ≫
    ((derivedTensor (ModuleCat.{u + 1} A) T).map
      ((compactificationEtaleComparison A e c).app M)).app K ≫
    (sfEtaleExactProjectionIso A c M K).hom = _
  rw [← Category.assoc, ← h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
end AlgebraicGeometry.Etale
