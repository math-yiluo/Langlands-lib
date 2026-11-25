/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.Ordinary.FiniteOrdinaryCompositeCoordinateArrow
public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.FiniteKummerBoundaryEquation

/-! # Arbitrary ordinary arrows in the finite coefficient coordinates

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: def-sfb-finite-ordinary-coordinate-arrow).
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

set_option linter.auxLemma false in
attribute [local instance 100000] Etale.DerivedCategoryModule._proof_1
  Etale.DerivedCategoryModule._proof_2
attribute [local instance 100000] Etale.ordinaryFiniteDerivedCategoryInstance
attribute [local implicit_reducible] Etale.ordinaryFiniteDegreeZero
  Etale.ordinaryFiniteSingleFunctor
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

/-- The comparison image of an arbitrary ordinary degree-two line arrow, in the
specified intrinsic coordinates. Source: the exact single and shift comparisons
(blueprint: def-sfb-finite-ordinary-coordinate-arrow). -/
def finiteOrdinaryCoordinateArrow (n : ℕ) [Finite (SpTowerShriek.R l E n)]
    (T : Scheme.{u}) {hT : IsUnit ((l ^ (n + 1) : ℕ) : Γ(T, ⊤))}
    (c : SpTowerP1.CoefficientCoordinates l E n T hT)
    (a : Etale.ordinaryFiniteUnit (FiniteRing l E n) T ⟶
      (Etale.ordinaryFiniteLine (FiniteRing l E n) (l ^ (n + 1))
        (ULift.ext (coefficient_annihilates l E n)) T)⟦(2 : ℤ)⟧) :
    finiteKummerUnit l E T n ⟶ finiteKummerLine l E T n :=
  finiteOrdinarySuccessiveCoordinateArrow l E n T
    (finiteOrdinaryUnitCoordinate l E n T c) (finiteOrdinaryLineCoordinate l E n T c) a

end AlgebraicGeometry.ProEtale.DiagonalTrace
