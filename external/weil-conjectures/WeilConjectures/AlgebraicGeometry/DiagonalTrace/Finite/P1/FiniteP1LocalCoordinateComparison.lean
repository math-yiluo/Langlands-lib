/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1OrdinaryCoordinateArrows
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryCoordinateArrow

import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1LocalCompositeEquation
import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryCoordinateViaSingle

/-! # Actual finite coordinate images of ordinary P1 and local arrows

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-p1-local-coordinate-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option cleanup.letToHave false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
set_option linter.auxLemma false in
-- Reuse the sheafification and localization witnesses stored in the endpoint maps.
attribute [local instance 100000] finiteKummerUnitCoordinate._proof_4
  finiteKummerUnitCoordinate._proof_5 finiteKummerUnitCoordinate._proof_9
  finiteKummerUnitCoordinate._proof_10
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
open SpTowerClasses
attribute [local instance 100000] CategoryTheory.Abelian.toPreadditive

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [local instance 100000] Etale.ordinaryFiniteDerivedCategoryInstance
attribute [local implicit_reducible] Etale.ordinaryFiniteDerivedCategoryInstance
  Etale.ordinaryFiniteSingleFunctor Etale.ordinaryFiniteDegreeZero
attribute [local irreducible] Functor.mapDerivedCategory SpTowerP1.nuSingle
  HasDerivedCategory.ofIsGrothendieckAbelian HomologicalComplex.quasiIso
  Etale.projectiveLineTraceTransport
  geoP1PullComparison
  Etale.ordinaryFiniteUnitPullback Etale.ordinaryFiniteShiftedLinePullback

/-- The local fixed-Hom coordinate image is successive ordinary coordinate
transport. Source: exact single comparison and the actual local-image equation
(blueprint: lem-sfb-finite-p1-local-coordinate-comparison).

Proof: compose finiteP1LocalCoordinateImage_composite with the proved generic
finiteOrdinaryCoordinateArrow_via_single formula. The successive arrow uses
exactly the given unit and line fields of c, by their defining equations. -/
theorem finiteP1LocalCoordinateImage_ordinary (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (X : Scheme.{u}) {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX)
    (b : Etale.ordinaryFiniteUnit (FiniteRing l E n) X ⟶
      (Etale.ordinaryFiniteLine (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext (coefficient_annihilates l E n)) X)⟦(2 : ℤ)⟧) :
    HEq (finiteP1LocalCoordinateImage l E n X c b)
      (finiteOrdinaryCoordinateArrow l E n X c b) := by
  have h := finiteP1LocalCoordinateImage_composite l E n X c b
  have hn := finiteOrdinaryCoordinateArrow_via_single l E n X c.unit c.line b
  apply h.trans
  simpa only [finiteOrdinaryCoordinateArrow, finiteOrdinaryUnitCoordinate,
    finiteOrdinaryLineCoordinate] using heq_of_eq hn

end AlgebraicGeometry.ProEtale.DiagonalTrace
