import Langlands.GroupScheme.MatrixRepresentation.AdditiveFrobeniusOperators
import Langlands.GroupScheme.MatrixRepresentationTensor

/-! # Coefficients of actual additive tensor representations -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj Matrix Polynomial Kronecker TensorProduct

namespace Langlands.GroupScheme.MatrixRepresentation.AdditiveTensorCoefficients

open AdditiveDividedPowers AdditiveFrobeniusOperators

variable {k : Type u} [Field k]
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  (ρ : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) n)
  (σ : MatrixRepresentation (VectorGroup.groupScheme (CommRingCat.of k) 1) m)

/-- The tensor of two actual coefficient operators in product-basis coordinates. -/
def tensorCoefficientOperator (a b : ℕ) : Module.End k (n × m → k) :=
  Matrix.toLin' (coefficientMatrix ρ a ⊗ₖ coefficientMatrix σ b)

/-- This coordinate operator acts on the full module tensor product. -/
theorem tensorCoefficientOperator_coordinates (a b : ℕ)
    (v : (n → k) ⊗[k] (m → k)) :
    tensorCoefficientOperator ρ σ a b (CoordinateTensor.coordinates k n m v) =
      CoordinateTensor.coordinates k n m
        (TensorProduct.map (dividedPower ρ a) (dividedPower σ b) v) := by
  rw [CoordinateTensor.coordinates_map, dividedPower_eq_toLin,
    dividedPower_eq_toLin, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_toLin']
  rfl

/-- The universal univariate matrix is the Kronecker product of the two matrices. -/
theorem univariateMatrix_tensor :
    univariateMatrix (ρ.tensor σ) = univariateMatrix ρ ⊗ₖ univariateMatrix σ := by
  funext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp only [univariateMatrix, VectorGroupPolynomial.polynomialMatrix, Matrix.map_apply,
    Matrix.kronecker_apply]
  rw [tensor_affineMatrix]
  simp only [GeneralLinear.kroneckerHom_coe, Matrix.kronecker_apply, map_mul]

/-- Each actual tensor coefficient is the convolution of the factor coefficients. -/
theorem coefficientMatrix_tensor (d : ℕ) :
    coefficientMatrix (ρ.tensor σ) d =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal d,
        coefficientMatrix ρ ab.1 ⊗ₖ coefficientMatrix σ ab.2 := by
  funext i j
  rcases i with ⟨i₁, i₂⟩
  rcases j with ⟨j₁, j₂⟩
  simp only [coefficientMatrix, univariateMatrix_tensor, Matrix.kronecker_apply,
    Polynomial.coeff_mul, Matrix.sum_apply]

/-- The convolution identity for the actual coefficient endomorphisms. -/
theorem dividedPower_tensor (d : ℕ) :
    dividedPower (ρ.tensor σ) d =
      ∑ ab ∈ Finset.HasAntidiagonal.antidiagonal d, tensorCoefficientOperator ρ σ ab.1 ab.2 := by
  rw [dividedPower_eq_toLin, coefficientMatrix_tensor, map_sum]
  rfl

variable (p : ℕ) [Fact p.Prime] [CharP k p]

/-- Below degree p^e only the constant coefficient of the powered factor contributes. -/
theorem coefficientMatrix_tensor_frobeniusPower_of_lt (e d : ℕ) (hd : d < p ^ e) :
    coefficientMatrix (ρ.tensor (σ.frobeniusPower p e)) d =
      coefficientMatrix ρ d ⊗ₖ (1 : Matrix m m k) := by
  rw [coefficientMatrix_tensor]
  have hsum :
      (∑ ab ∈ Finset.HasAntidiagonal.antidiagonal d,
        coefficientMatrix ρ ab.1 ⊗ₖ
          coefficientMatrix (σ.frobeniusPower p e) ab.2) =
        coefficientMatrix ρ d ⊗ₖ coefficientMatrix (σ.frobeniusPower p e) 0 := by
    apply Finset.sum_eq_single (d, 0)
    · intro ab hab hne
      have hab' := Finset.HasAntidiagonal.mem_antidiagonal.mp hab
      have hbpos : 0 < ab.2 := by
        rcases ab with ⟨a, b⟩
        simp only [ne_eq, Prod.mk.injEq] at hne
        dsimp at hab' ⊢
        omega
      have hblt : ab.2 < p ^ e := by omega
      have hnot : ¬ p ^ e ∣ ab.2 := by
        intro hdiv
        exact (Nat.not_le.mpr hblt) (Nat.le_of_dvd hbpos hdiv)
      rw [coefficientMatrix_frobeniusPower_of_not_dvd σ p e ab.2 hnot,
        Matrix.kronecker_zero]
    · intro h
      exact (h (Finset.HasAntidiagonal.mem_antidiagonal.mpr (Nat.add_zero d))).elim
  rw [hsum, coefficientMatrix_zero]

/-- Low coefficient endomorphisms act only on the first tensor factor. -/
theorem dividedPower_tensor_frobeniusPower_of_lt (e d : ℕ) (hd : d < p ^ e) :
    dividedPower (ρ.tensor (σ.frobeniusPower p e)) d =
      Matrix.toLin' (coefficientMatrix ρ d ⊗ₖ (1 : Matrix m m k)) := by
  rw [dividedPower_eq_toLin, coefficientMatrix_tensor_frobeniusPower_of_lt ρ σ p e d hd]

/-- On the full tensor product, a low coefficient is D_d tensor the identity. -/
theorem dividedPower_tensor_frobeniusPower_coordinates_of_lt
    (e d : ℕ) (hd : d < p ^ e) (v : (n → k) ⊗[k] (m → k)) :
    dividedPower (ρ.tensor (σ.frobeniusPower p e)) d
        (CoordinateTensor.coordinates k n m v) =
      CoordinateTensor.coordinates k n m
        (TensorProduct.map (dividedPower ρ d) LinearMap.id v) := by
  rw [dividedPower_tensor_frobeniusPower_of_lt ρ σ p e d hd,
    CoordinateTensor.coordinates_map, dividedPower_eq_toLin,
    LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id]
  rfl

end Langlands.GroupScheme.MatrixRepresentation.AdditiveTensorCoefficients
