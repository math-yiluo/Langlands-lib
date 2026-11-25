/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1KummerCoordinates

/-! # The evaluated Chern arrow through the finite evaluation coordinate

Source: diagonal-tower trace (1), normalized finite positive Kummer class before direct image.
(blueprint: lem-sfb-finite-p1-kummer-evaluated).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

/-- The evaluated first Chern arrow is the inverse single comparison, the evaluated
tower Chern arrow, and the finite evaluation coordinate.

Source: classes (2) of the diagonal-tower trace
(blueprint: lem-sfb-finite-p1-kummer-evaluated).

Proof: unfold evaluatedChern, mapSingleArrow and finiteKummerEvaluation; both sides
are the same composite of the single comparison, the evaluated arrow, the shift
comparison and the shifted line evaluation, up to reassociation. -/
theorem finiteP1_evaluatedChern_eq (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X : Scheme.{u}} (cX : Chern l E X) (L : Scheme.Pic X) (n : ℕ) :
    evaluatedChern l E cX L n =
      ((SpTowerShriek.ev l E X n).mapDerivedCategorySingleFunctor 0).inv.app _ ≫
        (SpTowerShriek.Ev l E X n).map (firstChern l E cX L) ≫
        (finiteKummerEvaluation l E cX n).hom := by
  simp only [evaluatedChern, mapSingleArrow, finiteKummerEvaluation, Iso.trans_hom,
    Functor.mapIso_hom, Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry.ProEtale.DiagonalTrace
