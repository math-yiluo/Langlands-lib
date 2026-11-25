/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralBoundaryData
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Scalar.TowerScalarFiniteBoundaryData

import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Chern.TowerChernEvaluationComparison
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Integral.TowerIntegralEvaluationComparison
import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Kummer.TowerKummerEvaluationComparison

/-! # Combining integral normalization and scalar finite compatibility -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u u₁ v₁
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.SpTowerClasses

private theorem finiteBoundaryEquality_transport {D : Type u₁} [Category.{v₁} D]
    {X X' Y Y' : D} (q : X ⟶ X') (r : Y ⟶ Y')
    {A B A' B' : Type v₁} {a : A} {b : B} {a' : A'} {b' : B'}
    (ha : HEq a a') (hb : HEq b b') (h : finiteBoundaryEquality q r a b) :
    finiteBoundaryEquality q r a' b' := by
  rcases h with ⟨x, y, hx, hy, hxy⟩
  exact ⟨x, y, hx.trans ha, hy.trans hb, hxy⟩

/-- Integral boundary normalization and scalar compatibility give finite Chern normalization.
Source: blueprint latest, `sk-prop-sp-tower-geometric-classes.proof.md`, clause (2),
final evaluation of the constructed first Chern arrow.
(blueprint: lem-sfb-chern-finite-assembly).

Proof: at each line bundle L and level n, apply the scalar comparison to the
integral arrow defined by the unit inverse, reduction of lineBundleClass, and
root comparison. Replace its underlying integral arrow by the positive Kummer
composite using the integral normalization. The scalar extension and evaluation
of that integral arrow are exactly the existing firstChern and evaluatedChern
formulas. The resulting boundary equality is the stated finite normalization. -/
theorem finiteChernNormalization_of_arrowComparisons (l : ℕ) [Fact l.Prime]
    (E : Type u) [Field E] [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {T : Scheme.{u}} (c : Chern l E T)
    (hi : ∀ L : T.Pic, IntegralBoundaryNormalization l
      (Rrings l T) (Arings l E T) (coefficientSystemMap l E T) c (lineBundleClass T L))
    (hs : ∀ (f : unit T (Rrings l T) ⟶
        ((DerivedCategory.singleFunctor (Systems T (Rrings l T)) 0).obj
          c.rootModule)⟦(2 : ℤ)⟧) (n : ℕ), ScalarFiniteBoundary l E c f n) :
    FiniteChernNormalization l E c := by
  intro L n
  exact finiteBoundaryEquality_transport _ _
    (forgetEvaluatedArrow_firstChernR l E c L n)
    (integralEvaluation_of_normalization l
      (Rrings l T) (Arings l E T) (coefficientSystemMap l E T) c
      (lineBundleClass T L) n (hi L) |>.trans
        (towerKummerBoundary_evaluation l c.kummer (lineBundleClass T L) n))
    (hs (firstChernR l E c L) n).out

end AlgebraicGeometry.ProEtale.SpTowerClasses

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
