/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassArrowTransport
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarChernArrow

/-! # The scalar and finite comparison for an arbitrary integral arrow -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

/-- The scalar/finite comparison for an arbitrary integral arrow.
Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2).
(blueprint: def-sfb-scalar-finite-boundary).
Fact wraps the actual finiteBoundaryEquality after scalarChernArrow, evaluation,
forgetting, and the fixed integer and root maps. The integral arrow is arbitrary
and no Kummer boundary or its normalization is part of this proposition. -/
def ScalarFiniteBoundary (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ) : Prop :=
  Fact <|
    let a := forgetEvaluatedArrow (C := Systems T (Arings l E T))
        (SpTowerShriek.ev l E T n) (finiteForget l E T n) (lineEvaluation l E c n)
        (scalarChernArrow l E c f)
    let beta := mapSingleArrow (abEvaluation T n) (2 : ℤ)
        (underlyingChernArrow l c f)
    finiteBoundaryEquality
      ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map (finiteQuotient l E T n))
      (((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
        (finiteRootMap l E T n))⟦(2 : ℤ)⟧')
      a beta

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
