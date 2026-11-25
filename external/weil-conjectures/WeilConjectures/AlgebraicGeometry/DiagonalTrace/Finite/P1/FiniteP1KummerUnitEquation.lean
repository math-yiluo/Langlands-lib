/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1KummerCoordinates

/-! # The finite source coordinate through the single comparison

Source: diagonal-tower trace (1), normalized finite positive Kummer class before direct image.
(blueprint: lem-sfb-finite-p1-kummer-unit-equation).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

/-- The normalized source coordinate on X is the exact single-complex comparison of
evaluation followed by the finite source coordinate.

Source: diagonal-tower trace (1), coefficient units
(blueprint: lem-sfb-finite-p1-kummer-unit-equation).

Proof: unfold both coordinates. Each is the composite of the single comparison of
evaluation, the single complex of the inverse of c.unit, the inverse of nuSingle and
the inverse ordinary unit pullback along e; the two sides differ only by
reassociation. -/
theorem finiteP1_unit_coordinate_eq (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    {X S : Scheme.{u}} (e : X ≅ ProjectiveLine S)
    (n : ℕ) {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX) :
    (finiteOverUnitCoordinate l E n e c).hom =
      ((SpTowerShriek.ev l E X n).mapDerivedCategorySingleFunctor 0).hom.app _ ≫
        (finiteKummerUnitCoordinate l E n e c).hom := by
  simp only [finiteOverUnitCoordinate, finiteUnitCoordinate, finiteKummerUnitCoordinate,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv, Functor.mapIso_inv,
    Functor.mapIso_hom, Iso.app_hom, Category.assoc]

end AlgebraicGeometry.ProEtale.DiagonalTrace
