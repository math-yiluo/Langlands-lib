/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralTowerBoundary
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteEvaluatedKummerComposite
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteEvaluatedIntegralLineClass
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus

/-! # Evaluating the integral Kummer composite

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-integral-boundary-evaluation-map).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u u₁ v₁ u₂ v₂ w₁ w₂ t₁ t₂
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
open FiniteExactArrow
attribute [local instance 100001] finiteIntegralTowerDerived finiteIntegralTowerExt
  finiteIntegralAbDerived finiteIntegralAbExt

attribute [local implicit_reducible] diagonalAbSheafAbelian towerAbelian constant

attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard DerivedCategory.singleFunctors
  integerComparison cartierRootsComparison cartierUnitsComparison

/-- Exact evaluation preserves the integral connecting composite.
Source: exact-functor naturality of Yoneda composition
(blueprint: lem-sfb-finite-integral-boundary-evaluation-map). -/
theorem finiteIntegralBoundary_evaluation_map (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (k : Kummer l T) (n : ℕ) (L : T.Pic) :
    @Eq (FiniteIntegralBoundaryArrow l T n)
      (finiteEvaluatedIntegralBoundary l T k n L)
      (finiteEvaluatedKummerComposite l T k n
        (finiteEvaluatedIntegralLineClass T n L)) := by
  exact mapSingleArrow_kummerComposite (abEvaluation T n) k.exact (lineBundleClass T L)

end AlgebraicGeometry.ProEtale.SpTowerClasses
