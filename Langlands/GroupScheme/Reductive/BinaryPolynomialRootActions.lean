import Langlands.GroupScheme.Reductive.HomogeneousPolynomialRepresentation
import Mathlib.Data.Nat.Choose.Sum

/-! # Root transvections on binary homogeneous polynomials -/

noncomputable section

universe u

namespace Langlands.GroupScheme.HomogeneousPolynomial

open MvPolynomial Matrix

variable {R : Type u} [CommRing R]

/-- The actual upper root element in the special linear group of rank two. -/
def upperRoot (t : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  Matrix.SpecialLinearGroup.transvection (i := 0) (j := 1) (by decide) t

/-- The actual lower root element in the special linear group of rank two. -/
def lowerRoot (t : R) : Matrix.SpecialLinearGroup (Fin 2) R :=
  Matrix.SpecialLinearGroup.transvection (i := 1) (j := 0) (by decide) t

@[simp]
theorem upperRoot_X_zero (t : R) :
    substitution (upperRoot t : Matrix (Fin 2) (Fin 2) R) (X 0) = X 0 := by
  simp [upperRoot, substitution_X, variableImage,
    Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.one_apply, Matrix.single]

@[simp]
theorem upperRoot_X_one (t : R) :
    substitution (upperRoot t : Matrix (Fin 2) (Fin 2) R) (X 1) = C t * X 0 + X 1 := by
  simp [upperRoot, substitution_X, variableImage,
    Matrix.SpecialLinearGroup.transvection_coe, Fin.sum_univ_two,
    Matrix.one_apply, Matrix.single]

@[simp]
theorem lowerRoot_X_zero (t : R) :
    substitution (lowerRoot t : Matrix (Fin 2) (Fin 2) R) (X 0) = X 0 + C t * X 1 := by
  simp [lowerRoot, substitution_X, variableImage,
    Matrix.SpecialLinearGroup.transvection_coe, Fin.sum_univ_two,
    Matrix.one_apply, Matrix.single]

@[simp]
theorem lowerRoot_X_one (t : R) :
    substitution (lowerRoot t : Matrix (Fin 2) (Fin 2) R) (X 1) = X 1 := by
  simp [lowerRoot, substitution_X, variableImage,
    Matrix.SpecialLinearGroup.transvection_coe,
    Matrix.one_apply, Matrix.single]

/-- The binomial formula for the upper root on every binary monomial. -/
theorem upperRoot_monomial (t : R) (a b : ℕ) :
    substitution (upperRoot t : Matrix (Fin 2) (Fin 2) R) (X 0 ^ a * X 1 ^ b) =
      ∑ r ∈ Finset.range (b + 1),
        C ((b.choose r : R) * t ^ r) * (X 0 ^ (a + r) * X 1 ^ (b - r)) := by
  rw [map_mul, map_pow, map_pow, upperRoot_X_zero, upperRoot_X_one, add_pow,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [mul_pow, ← map_pow, map_mul, map_natCast, pow_add]
  ring

/-- The binomial formula for the lower root on every binary monomial. -/
theorem lowerRoot_monomial (t : R) (a b : ℕ) :
    substitution (lowerRoot t : Matrix (Fin 2) (Fin 2) R) (X 0 ^ a * X 1 ^ b) =
      ∑ r ∈ Finset.range (a + 1),
        C ((a.choose r : R) * t ^ r) * (X 0 ^ (a - r) * X 1 ^ (b + r)) := by
  rw [map_mul, map_pow, map_pow, lowerRoot_X_zero, lowerRoot_X_one,
    add_comm (X 0) (C t * X 1), add_pow, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [mul_pow, ← map_pow, map_mul, map_natCast, pow_add]
  ring

end Langlands.GroupScheme.HomogeneousPolynomial
