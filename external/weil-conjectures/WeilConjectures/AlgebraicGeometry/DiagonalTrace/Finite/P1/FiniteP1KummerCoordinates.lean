/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.P1.FiniteP1CoefficientAdjunctionCoordinates
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.FiniteKummerBoundaryEquation
import WeilConjectures.AlgebraicGeometry.FiniteP1UnitOnPullback
import Mathlib.AlgebraicGeometry.Scheme

/-! # Normalized finite Kummer coordinates

Source: diagonal-tower trace proof (1), comparison with the finite positive Kummer class.
(blueprint: def-sfb-finite-p1-kummer-coordinates).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale.DiagonalTrace
open SpTowerClasses

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- Evaluation followed by the specified finite root-line identification.
Source: exact single and shift comparisons
(blueprint: def-sfb-finite-p1-kummer-coordinates). -/
def finiteKummerEvaluation {T : Scheme.{u}} (cT : Chern l E T) (n : ℕ) :
    (SpTowerShriek.Ev l E T n).obj ((line l E cT)⟦(2 : ℤ)⟧) ≅
      finiteKummerLine l E T n :=
  ((SpTowerShriek.Ev l E T n).commShiftIso (2 : ℤ)).app _ ≪≫
    (shiftFunctor _ (2 : ℤ)).mapIso
      (((SpTowerShriek.ev l E T n).mapDerivedCategorySingleFunctor 0).app _ ≪≫
        (DerivedCategory.singleFunctor _ 0).mapIso (lineEvaluation l E cT n))

/-- The source coordinate before the tower single-complex comparison.
Source: constant-section normalization
(blueprint: def-sfb-finite-p1-kummer-coordinates). -/
def finiteKummerUnitCoordinate (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    {X S : Scheme.{u}} (e : X ≅ ProjectiveLine S)
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX) :
    finiteKummerUnit l E X n ≅
      (finiteOverRealization l E n e).obj
        (geoP1Unit (FiniteRing l E n) (ProjectiveLine S)) :=
  ((DerivedCategory.singleFunctor _ 0).mapIso c.unit).symm ≪≫
    (SpTowerP1.nuSingle l E n X _).symm ≪≫
    (Functor.mapDerivedCategory
      (Scheme.sfIntrinsicModuleEquivalence X (SpTowerShriek.R l E n)).functor).mapIso
      (geoP1UnitPullback (FiniteRing l E n) e.hom).symm

/-- The normalized target coordinate; it depends only on the finite roots, not on c1.
Source: the roots-section-normalized line comparison and pullback along e
(blueprint: def-sfb-finite-p1-kummer-coordinates). -/
def finiteKummerLineCoordinate (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    {X S : Scheme.{u}} (e : X ≅ ProjectiveLine S)
    (hS : IsUnit (l : Γ(S, ⊤)))
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX) :
    finiteKummerLine l E X n ≅
      (finiteOverRealization l E n e).obj
        (geoP1Twist (FiniteRing l E n) (l ^ (n + 1))
          (ULift.ext (coefficient_annihilates l E n)) (ProjectiveLine S) 1 2) :=
  ((shiftFunctor _ (2 : ℤ)).mapIso
    ((SpTowerP1.nuSingle l E n X _) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso c.line)).symm ≪≫
    ((SpTowerP1.nu l E n X).commShiftIso (2 : ℤ)).symm.app _ ≪≫
    (Functor.mapDerivedCategory
      (Scheme.sfIntrinsicModuleEquivalence X (SpTowerShriek.R l E n)).functor).mapIso
      (geoP1TwistPullback (FiniteRing l E n) (l ^ (n + 1))
        (pow_pos (Fact.out : l.Prime).pos _)
        (ULift.ext (coefficient_annihilates l E n)) e.hom
        (finiteP1_unitOnPullback (l ^ (n + 1)) (ProjectiveLine S ↘ S)
          (by simpa only [Nat.cast_pow] using hS.pow (n + 1))) 1 2).symm

/-- The normalized isomorphism retained as data, with no choice from mere existence.
Source: the single, line, shift and site comparisons
(blueprint: def-sfb-finite-p1-kummer-coordinates). -/
def finiteP1KummerCoordinate (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    {X S : Scheme.{u}} (e : X ≅ ProjectiveLine S) (cX : Chern l E X)
    (hS : IsUnit (l : Γ(S, ⊤)))
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX) :=
  finiteKummerEvaluation l E cX n ≪≫ finiteKummerLineCoordinate l E n e hS c

/-- The ordinary positive Chern arrow in finite intrinsic single-complex coordinates.
It contains no tower Chern arrow or assumed boundary equation.
Source: the ordinary finite Kummer normalization
(blueprint: def-sfb-finite-p1-kummer-coordinates). -/
def finiteP1OrdinaryKummerArrow (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    {X S : Scheme.{u}} [IsNoetherian S] (e : X ≅ ProjectiveLine S)
    (hS : IsUnit (l : Γ(S, ⊤)))
    {hX : IsUnit ((l ^ (n + 1) : ℕ) : Γ(X, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n X hX) :
    finiteKummerUnit l E X n ⟶ finiteKummerLine l E X n :=
  (finiteKummerUnitCoordinate l E n e c).hom ≫
    (finiteOverRealization l E n e).map
      ((geoP1Comparison (FiniteRing l E n) (ProjectiveLine S)).map
        (geoP1EtaleChern (FiniteRing l E n) (l ^ (n + 1))
          (pow_pos (Fact.out : l.Prime).pos _)
          (ULift.ext (coefficient_annihilates l E n)) S
          (by simpa only [Nat.cast_pow] using hS.pow (n + 1)))) ≫
    (finiteKummerLineCoordinate l E n e hS c).inv

end AlgebraicGeometry.ProEtale.DiagonalTrace
