/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteEvaluatedIntegralLineClass
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.FiniteExactArrow.FiniteExactArrowCalculus

/-! # Evaluating the integral Kummer composite

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-integral-line-class-evaluation).
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

attribute [local implicit_reducible] diagonalAbSheafAbelian towerAbelian constant

attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard DerivedCategory.singleFunctors
  integerComparison cartierRootsComparison cartierUnitsComparison

/-- Exact evaluation cancels the constant-system transport of the actual line
bundle class. Source: the definition of lineBundleClass and exact functor composition
(blueprint: lem-sfb-finite-integral-line-class-evaluation). -/
theorem finiteIntegralLineClass_evaluation (T : Scheme.{u}) (n : ℕ) (L : T.Pic) :
    finiteEvaluatedIntegralLineClass T n L =
      lineBundleEtaleClass T L := by
  exact mapSingleArrow_eval_const (C := DiagonalAb T) (op n) 1
    (lineBundleEtaleClass T L)

end AlgebraicGeometry.ProEtale.SpTowerClasses
