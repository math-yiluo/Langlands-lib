/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralCategoryWitnesses

/-! # The integral Kummer composite and exact evaluation

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: def-sfb-finite-integral-tower-boundary).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u u₁ v₁ u₂ v₂ w₁ w₂ t₁ t₂
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [local instance 100001] finiteIntegralTowerDerived finiteIntegralTowerExt
  finiteIntegralAbDerived finiteIntegralAbExt finiteIntegralEtaleDerived finiteIntegralEtaleExt

attribute [local irreducible] Functor.mapDerivedCategory Ext.homEquiv
  HasDerivedCategory.standard DerivedCategory.singleFunctors
  integerComparison cartierRootsComparison cartierUnitsComparison

/-- The integral tower boundary, with its single-complex endpoints cached.
Source: the Yoneda composite defining the Kummer first Chern class
(blueprint: def-sfb-finite-integral-tower-boundary). -/
def finiteIntegralTowerBoundary (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (k : Kummer l T) (L : T.Pic) :
    (DerivedCategory.singleFunctor (Ab T) 0).obj (integers T) ⟶
      ((DerivedCategory.singleFunctor (Ab T) 0).obj (roots l T))⟦(2 : ℤ)⟧ :=
  kummerComposite (C := Ab T) (ShortComplex.mk k.inclusion k.power k.zero) k.exact
    (lineBundleClass T L)

/-- Exact evaluation of the integral tower boundary.
Source: evaluation of the Kummer composite at a positive coefficient level
(blueprint: def-sfb-finite-integral-tower-boundary). -/
def finiteEvaluatedIntegralBoundary (l : ℕ) [Fact l.Prime] (T : Scheme.{u})
    (k : Kummer l T) (n : ℕ) (L : T.Pic) :
    FiniteIntegralBoundaryArrow l T n :=
  mapSingleArrow (C := Ab T) (D := DiagonalAb T) (abEvaluation T n)
    (X := integers T) (Y := roots l T) (2 : ℤ) (finiteIntegralTowerBoundary l T k L)

end AlgebraicGeometry.ProEtale.SpTowerClasses
