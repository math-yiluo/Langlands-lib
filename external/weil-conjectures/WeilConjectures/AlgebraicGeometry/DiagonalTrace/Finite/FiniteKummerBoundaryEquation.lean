/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Class.TowerClassFinite
public import WeilConjectures.AlgebraicGeometry.SpTowerClasses.Finite.FiniteIntegralTowerBoundary

/-! # A shared finite Kummer boundary equation

Source: finite Kummer normalization.
(blueprint: def-sfb-finite-kummer-boundary-equation).
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

/-- The regular coefficient single complex in the finite intrinsic presentation.
Source: coefficient evaluation (blueprint: def-sfb-finite-kummer-boundary-equation). -/
abbrev finiteKummerUnit (T : Scheme.{u}) (n : ℕ) :=
  (DerivedCategory.singleFunctor _ 0).obj
    ((SpTowerShriek.ev l E T n).obj (coefficient T (Arings l E T)))

/-- The scalar-extended roots single complex, shifted by two.
Source: positive Kummer class (blueprint: def-sfb-finite-kummer-boundary-equation). -/
abbrev finiteKummerLine (T : Scheme.{u}) (n : ℕ) :=
  ((DerivedCategory.singleFunctor _ 0).obj (finiteLine l E T n))⟦(2 : ℤ)⟧

/-- The integral Kummer boundary equation, sharing the finite category witnesses.
Source: finite Kummer normalization
(blueprint: def-sfb-finite-kummer-boundary-equation). -/
def FiniteKummerBoundary (T : Scheme.{u}) (n : ℕ) (k : Kummer l T) (L : T.Pic)
    (a : finiteKummerUnit l E T n ⟶ finiteKummerLine l E T n) : Prop :=
  finiteBoundaryEquality
    ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map (finiteQuotient l E T n))
    (((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
      (finiteRootMap l E T n))⟦(2 : ℤ)⟧')
    (mapSingleArrow (finiteForget l E T n) (2 : ℤ) a)
    (finiteEvaluatedIntegralBoundary l T k n L)

end AlgebraicGeometry.ProEtale.DiagonalTrace
