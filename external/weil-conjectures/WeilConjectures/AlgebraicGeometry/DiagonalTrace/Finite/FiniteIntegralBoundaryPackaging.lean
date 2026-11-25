/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalTrace.Finite.FiniteKummerBoundaryEquation

/-! # Arbitrary ordinary arrows in the finite coefficient coordinates

Source: diagonal-tower trace (1), finite Kummer classes and exact comparison.
(blueprint: lem-sfb-finite-integral-boundary-packaging).
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
open SpTowerClasses
attribute [local irreducible] Padic Padic.coefficientExtensionIntegers
variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

private theorem boundary_of_eq {D : Type*} [Category D]
    {X X' Y Y' : D} (q : X ⟶ X') (r : Y ⟶ Y')
    (a : X' ⟶ Y') (b : X ⟶ Y) (h : q ≫ a = b ≫ r) :
    finiteBoundaryEquality q r a b := ⟨a, b, HEq.rfl, HEq.rfl, h⟩

/-- A concrete integral boundary equation supplies its fixed endpoint witnesses.
Source: the definition of finiteBoundaryEquality
(blueprint: lem-sfb-finite-integral-boundary-packaging). -/
theorem finiteKummerBoundary_of_integral_eq (T : Scheme.{u}) (n : ℕ)
    (k : Kummer l T) (L : T.Pic)
    (a : finiteKummerUnit l E T n ⟶ finiteKummerLine l E T n)
    (h : (DerivedCategory.singleFunctor (DiagonalAb T) 0).map (finiteQuotient l E T n) ≫
        mapSingleArrow (finiteForget l E T n) (2 : ℤ) a =
      finiteEvaluatedIntegralBoundary l T k n L ≫
        ((DerivedCategory.singleFunctor (DiagonalAb T) 0).map
          (finiteRootMap l E T n))⟦(2 : ℤ)⟧') :
    FiniteKummerBoundary l E T n k L a := by
  exact boundary_of_eq _ _ _ _ h

end AlgebraicGeometry.ProEtale.DiagonalTrace
