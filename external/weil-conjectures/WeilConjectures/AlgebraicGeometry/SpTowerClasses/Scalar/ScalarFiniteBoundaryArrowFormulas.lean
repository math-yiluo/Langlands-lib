/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.ScalarFiniteBoundaryArrows
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteBoundaryExactTransport
/-! # Formulas for the finite scalar and integral evaluation arrows -/
@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u
open CategoryTheory CategoryTheory.Limits Opposite WeilConjectures
namespace AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [local implicit_reducible] spCoefficientCommRings
attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- Scalar evaluation is exact transport followed by its finite target map.
Source: the exact transport laws (blueprint: lem-sfb-finite-boundary-arrow-formulas).
Proof: apply forgetEvaluatedArrow_eq to the two exact functors in the definition. -/
theorem scalarFiniteBoundary_eval_eq (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ) :
    scalarFiniteBoundary_eval l E c f n =
      mapSingleArrow (SpTowerShriek.ev l E T n ⋙ finiteForget l E T n) (2 : ℤ)
          (scalarChernArrow l E c f) ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          ((finiteForget l E T n).map (lineEvaluation l E c n).hom))⟦(2 : ℤ)⟧' := by
  exact forgetEvaluatedArrow_eq (SpTowerShriek.ev l E T n) (finiteForget l E T n)
    (lineEvaluation l E c n) (scalarChernArrow l E c f)

/-- Integral evaluation is exact transport with the evaluated ordinary endpoints.
Source: the exact transport laws (blueprint: lem-sfb-finite-boundary-arrow-formulas).
Proof: apply map_underlyingSingleArrow to the definition of underlyingChernArrow. -/
theorem scalarFiniteBoundary_integral_eq (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (f : unit T (Rrings l T) ⟶
      ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
        c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ) :
    scalarFiniteBoundary_integral l E c f n =
      (DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          ((abEvaluation T n).map
            (integerGenerator T (Rrings l T) c.reduction.forget)) ≫
        mapSingleArrow (c.reduction.forget.F ⋙ abEvaluation T n) (2 : ℤ) f ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          ((abEvaluation T n).map c.rootForget.hom))⟦(2 : ℤ)⟧' := by
  exact map_underlyingSingleArrow c.reduction.forget.F (abEvaluation T n)
    (integerGenerator T (Rrings l T) c.reduction.forget) c.rootForget.hom f
end AlgebraicGeometry.ProEtale.SpTowerClasses
attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
