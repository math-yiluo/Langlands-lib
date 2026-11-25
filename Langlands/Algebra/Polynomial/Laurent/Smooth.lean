module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.RingTheory.Smooth.Basic

/-! # Smoothness of the Laurent polynomial algebra

For a commutative ring `R`, the algebra `R[T;T⁻¹]` is smooth over `R`
(`LaurentPolynomial.instSmooth`): it is the localization of the polynomial algebra `R[X]` away
from `X`, and both steps are smooth. The scalar tower `R → R[X] → R[T;T⁻¹]` along
`Polynomial.toLaurent` is the instance `LaurentPolynomial.isScalarTower_polynomial`.
-/

public section

open Polynomial

namespace LaurentPolynomial

/-- The scalar tower `R → R[X] → R[T;T⁻¹]`: a constant polynomial goes to the constant Laurent
polynomial. -/
instance isScalarTower_polynomial (R : Type*) [CommSemiring R] :
    IsScalarTower R R[X] R[T;T⁻¹] :=
  IsScalarTower.of_algebraMap_eq fun r => (Polynomial.toLaurent_C r).symm

/-- The Laurent polynomial algebra is smooth over its ring of coefficients. -/
instance instSmooth (R : Type*) [CommRing R] : Algebra.Smooth R R[T;T⁻¹] := by
  let : Algebra.Smooth R R[X] := {}
  let := Algebra.Smooth.of_isLocalization_Away (A := R[T;T⁻¹]) (X : R[X])
  apply Algebra.Smooth.comp R R[X]

end LaurentPolynomial
