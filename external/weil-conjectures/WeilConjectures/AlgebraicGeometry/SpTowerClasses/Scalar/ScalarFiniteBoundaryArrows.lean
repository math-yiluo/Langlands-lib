/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarFiniteBoundaryData

/-! # Scalar finite boundary evaluation arrows

The two original endpoint arrows, with their formulas unchanged.
(blueprint: def-sfb-finite-boundary-arrows). -/

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

/-- The scalar evaluation morphism used in the finite boundary composite. -/
def scalarFiniteBoundary_eval (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ) :=
  forgetEvaluatedArrow (SpTowerShriek.ev l E T n) (finiteForget l E T n)
    (lineEvaluation l E c n) (scalarChernArrow l E c f)

/-- The integral evaluation morphism used in the finite boundary composite. -/
def scalarFiniteBoundary_integral (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ) :=
  mapSingleArrow (abEvaluation T n) (2 : ℤ) (underlyingChernArrow l c f)

end AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
