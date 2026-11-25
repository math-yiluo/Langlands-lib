/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1OrdinaryCoordinateArrows
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryCompositeCoordinateArrow

/-! # Actual finite coordinate images of ordinary P1 and local arrows

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-p1-local-composite-equation).
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

/-- The fixed-Hom local image is the actual generic composite coordinate image.
Source: the original intrinsic single and shift comparison constructions
(blueprint: lem-sfb-finite-p1-local-composite-equation).

Proof: both constructors compose the inverse source single with nuSingle,
apply the same intrinsic realization to the same ordinary comparison arrow,
then compose the same commShift and shifted target single isomorphisms.
The original and cached category witnesses are the same existing localization;
heterogeneous reflexivity retains both literal endpoint presentations. -/
theorem finiteP1LocalCoordinateImage_composite (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (X : Scheme.{u}) {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX)
    (b : Etale.ordinaryFiniteUnit (FiniteRing l E n) X ⟶
      (Etale.ordinaryFiniteLine (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext (coefficient_annihilates l E n)) X)⟦(2 : ℤ)⟧) :
    HEq (finiteP1LocalCoordinateImage l E n X c b)
      (finiteOrdinaryCompositeCoordinateArrow l E n X c.unit c.line b) := by
  rfl

end AlgebraicGeometry.ProEtale.DiagonalTrace
