import Langlands.AlgebraicGeometry.ProjectiveSpace
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.RingTheory.MvPolynomial.Basic

/-! # Homogeneous linear polynomials and coordinate linear forms -/

noncomputable section

open Module

namespace Langlands.AlgebraicGeometry.ProjectiveSpace

universe u

variable (R : Type u) [CommRing R] (n : ℕ)

/-- The actual coordinate variables form a basis of the degree-one submodule. -/
def degreeOneBasis :
    Basis (Fin (n + 1)) R (projectiveSpaceGrading R n 1) :=
  (Basis.span (MvPolynomial.linearIndependent_X (σ := Fin (n + 1)) (R := R))).map
    (LinearEquiv.ofEq _ _ MvPolynomial.homogeneousSubmodule_one_eq_span_X.symm)

@[simp]
theorem degreeOneBasis_coe (j : Fin (n + 1)) :
    (degreeOneBasis R n j : ProjectiveCoordinateRing R n) = MvPolynomial.X j := by
  simp only [degreeOneBasis, Basis.map_apply, Basis.span_apply]
  rfl

/-- A linear functional is exactly a homogeneous linear polynomial in these
coordinates. -/
def linearFormPolynomialEquiv :
    ((Fin (n + 1) → R) →ₗ[R] R) ≃ₗ[R] projectiveSpaceGrading R n 1 :=
  ((Pi.basisFun R (Fin (n + 1))).constr R).symm.trans (degreeOneBasis R n).equivFun.symm

theorem linearFormPolynomialEquiv_coe (ℓ : (Fin (n + 1) → R) →ₗ[R] R) :
    (linearFormPolynomialEquiv R n ℓ : ProjectiveCoordinateRing R n) =
      ∑ j, ℓ (Pi.single j 1) • MvPolynomial.X j := by
  simp [linearFormPolynomialEquiv, Basis.equivFun_symm_apply, Pi.basisFun_apply]

/-- Polynomial evaluation agrees with the original coordinate linear form. -/
@[simp]
theorem eval_linearFormPolynomialEquiv (ℓ : (Fin (n + 1) → R) →ₗ[R] R)
    (v : Fin (n + 1) → R) :
    MvPolynomial.eval v (linearFormPolynomialEquiv R n ℓ) = ℓ v := by
  rw [linearFormPolynomialEquiv_coe]
  change MvPolynomial.aeval v _ = _
  simp only [map_sum, map_smul, MvPolynomial.aeval_X, smul_eq_mul]
  have h := congrArg ℓ ((Pi.basisFun R (Fin (n + 1))).sum_repr v)
  simpa [map_sum, map_smul, Pi.basisFun_apply, mul_comm] using h

@[simp]
theorem linearFormPolynomialEquiv_coe_ne_zero (ℓ : (Fin (n + 1) → R) →ₗ[R] R) :
    (linearFormPolynomialEquiv R n ℓ : ProjectiveCoordinateRing R n) ≠ 0 ↔ ℓ ≠ 0 := by
  change ((linearFormPolynomialEquiv R n ℓ : ProjectiveCoordinateRing R n) ≠
    ((0 : projectiveSpaceGrading R n 1) : ProjectiveCoordinateRing R n)) ↔ ℓ ≠ 0
  rw [Subtype.coe_ne_coe]
  exact (linearFormPolynomialEquiv R n).map_ne_zero_iff

/-- Every actual homogeneous linear polynomial evaluates as its corresponding
linear functional. -/
theorem eval_eq_inverse_linearFormPolynomialEquiv (f : projectiveSpaceGrading R n 1)
    (v : Fin (n + 1) → R) :
    MvPolynomial.eval v f = (linearFormPolynomialEquiv R n).symm f v := by
  simpa using eval_linearFormPolynomialEquiv R n
    ((linearFormPolynomialEquiv R n).symm f) v

end Langlands.AlgebraicGeometry.ProjectiveSpace
