/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1KummerCoordinates

/-! # Actual finite coordinate images of ordinary P1 and local arrows

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: def-sfb-finite-p1-ordinary-coordinate-arrows).
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

/-- The actual original finite coordinate image of an ordinary P1 arrow.
Source: the specified projective-line endpoint coordinates
(blueprint: def-sfb-finite-p1-ordinary-coordinate-arrows). -/
def finiteP1CoordinateImage (n : ℕ)
    [Finite (SpTowerShriek.R l E n)] {X S : Scheme.{u}}
    (e : X ≅ ProjectiveLine S) (hS : IsUnit (l : Γ(S, ⊤)))
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX)
    (a : Etale.ordinaryFiniteUnit (FiniteRing l E n) (ProjectiveLine S) ⟶
      (Etale.ordinaryFiniteLine (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext (coefficient_annihilates l E n)) (ProjectiveLine S))⟦(2 : ℤ)⟧) :
    finiteKummerUnit l E X n ⟶ finiteKummerLine l E X n :=
  (finiteKummerUnitCoordinate l E n e c).hom ≫
    (finiteOverRealization l E n e).map
      ((geoP1Comparison (FiniteRing l E n) (ProjectiveLine S)).map a) ≫
    (finiteKummerLineCoordinate l E n e hS c).inv

/-- The actual composite-comparison image of a local ordinary arrow in the
fixed original finite Hom. Source: single and shift comparison
(blueprint: def-sfb-finite-p1-ordinary-coordinate-arrows). -/
def finiteP1LocalCoordinateImage (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (X : Scheme.{u}) {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX)
    (b : Etale.ordinaryFiniteUnit (FiniteRing l E n) X ⟶
      (Etale.ordinaryFiniteLine (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext (coefficient_annihilates l E n)) X)⟦(2 : ℤ)⟧) :
    finiteKummerUnit l E X n ⟶ finiteKummerLine l E X n :=
  (((DerivedCategory.singleFunctor _ 0).mapIso c.unit).symm ≪≫
      (SpTowerP1.nuSingle l E n X _).symm).hom ≫
    (Scheme.sfIntrinsicModuleEquivalence X
      (SpTowerShriek.R l E n)).functor.mapDerivedCategory.map
        ((geoP1Comparison (FiniteRing l E n) X).map b) ≫
    (((SpTowerP1.nu l E n X).commShiftIso (2 : ℤ)).app _ ≪≫
      (shiftFunctor _ (2 : ℤ)).mapIso
        ((SpTowerP1.nuSingle l E n X _) ≪≫
          (DerivedCategory.singleFunctor _ 0).mapIso c.line)).hom

end AlgebraicGeometry.ProEtale.DiagonalTrace
