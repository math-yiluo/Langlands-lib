import Langlands.Global.RankinSelberg.ComplexLocalCompactFourierAveraging
import Langlands.Global.RankinSelberg.ComplexSquareZetaCoefficientAverage
import Langlands.Global.RankinSelberg.ComplexSquareZetaPolynomialGaussian

/-! # Left compact averages of standard square polynomial Gaussians -/

noncomputable section

open MeasureTheory MvPolynomial
open scoped Matrix Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

open Langlands.Archimedean
open ComplexGodementGaussianPolynomial (Coordinates coordinates matrixSqNorm matrixGaussian
  matrixGaussian_mul_unitary gaussianPolynomial_apply exists_gaussianPolynomial_mul_unitary)
open ComplexJacquet (complexUnitaryInverseTranspose)

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Poly" => MvPolynomial (Coordinates n n) ℂ

private theorem matrixSqNorm_transpose (A : Mat) : matrixSqNorm Aᵀ = matrixSqNorm A := by
  unfold matrixSqNorm
  simp only [Matrix.transpose_apply]
  exact Finset.sum_comm

private def transposeVariables (p : Poly) : Poly :=
  rename (fun j => (j.2.1, j.1, j.2.2)) p

private theorem squarePolynomialGaussian_transpose (p : Poly) (A : Mat) :
    squarePolynomialGaussian (transposeVariables p) Aᵀ = squarePolynomialGaussian p A := by
  unfold squarePolynomialGaussian transposeVariables
  rw [eval_rename]
  change _ * (Real.exp (-(2 * Real.pi) * matrixSqNorm Aᵀ) : ℂ) =
    _ * (Real.exp (-(2 * Real.pi) * matrixSqNorm A) : ℂ)
  rw [matrixSqNorm_transpose]
  rfl

private theorem exists_right_squarePolynomialGaussian (p : Poly) (k : K) :
    ∃ q : Poly, q.totalDegree ≤ p.totalDegree ∧
      ∀ A : Mat, squarePolynomialGaussian p (A * k.val.val) = squarePolynomialGaussian q A := by
  obtain ⟨q, hq, hq'⟩ := exists_gaussianPolynomial_mul_unitary p k
  refine ⟨q, hq, fun A => ?_⟩
  have hG := matrixGaussian_mul_unitary A k
  have hNorm : matrixSqNorm (A * k.val.val) = matrixSqNorm A :=
    neg_injective (Real.exp_injective (Complex.ofReal_injective hG))
  have h := hq' A
  rw [gaussianPolynomial_apply, gaussianPolynomial_apply, hG] at h
  have hp := mul_right_cancel₀ (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _)) h
  change eval (coordinates (A * k.val.val)) p * (Real.exp (-(2 * Real.pi) * matrixSqNorm (A * k.val.val)) : ℂ) =
    eval (coordinates A) q * (Real.exp (-(2 * Real.pi) * matrixSqNorm A) : ℂ)
  rw [hNorm, hp]

/-- Left translation by an inverse unitary matrix preserves the standard Gaussian and bounds the
new polynomial degree by the degree of the original multiplier. -/
theorem exists_left_squarePolynomialGaussian (p : Poly) (k : K) :
    ∃ q : Poly, q.totalDegree ≤ p.totalDegree ∧
      ∀ A : Mat, squarePolynomialGaussian p (k.val⁻¹.val * A) = squarePolynomialGaussian q A := by
  let u := complexUnitaryInverseTranspose n k
  obtain ⟨q, hq, h⟩ := exists_right_squarePolynomialGaussian (transposeVariables p) u
  refine ⟨transposeVariables q, (totalDegree_rename_le _ _).trans
    (hq.trans (totalDegree_rename_le _ _)), fun A => ?_⟩
  calc
    _ = squarePolynomialGaussian (transposeVariables p) (Aᵀ * u.val.val) := by
      rw [← squarePolynomialGaussian_transpose p (k.val⁻¹.val * A), Matrix.transpose_mul]
      rfl
    _ = squarePolynomialGaussian q Aᵀ := h _
    _ = _ := by
      simpa only [Matrix.transpose_transpose] using (squarePolynomialGaussian_transpose q Aᵀ).symm

private def polynomialGaussianLinear (n : ℕ) :
    MvPolynomial (Coordinates n n) ℂ →ₗ[ℂ] (Matrix (Fin n) (Fin n) ℂ → ℂ) where
  toFun := squarePolynomialGaussian
  map_add' p q := by
    funext A
    simp only [squarePolynomialGaussian, map_add, Pi.add_apply, add_mul]
  map_smul' c p := by
    funext A
    simp only [squarePolynomialGaussian, MvPolynomial.smul_eq_C_mul, map_mul, eval_C,
      Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc]

/-- The inverse left unitary translates of a standard square polynomial Gaussian span a
finite-dimensional space. -/
theorem finiteDimensional_leftSquarePolynomialGaussian (Φ : 𝓢(Mat, ℂ)) (p : Poly)
    (hΦ : (Φ : Mat → ℂ) = squarePolynomialGaussian p) :
    FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k : K =>
      fun A : Mat => Φ (k.val⁻¹.val * A))) := by
  let L := polynomialGaussianLinear n
  let V := (restrictTotalDegree (Coordinates n n) ℂ p.totalDegree).map L
  refine Submodule.finiteDimensional_of_le (S₂ := V) (Submodule.span_le.mpr ?_)
  rintro _ ⟨k, rfl⟩
  obtain ⟨q, hq, hq'⟩ := exists_left_squarePolynomialGaussian p k
  refine ⟨q, (mem_restrictTotalDegree _ _ _).mpr hq, funext fun A => ?_⟩
  change squarePolynomialGaussian q A = Φ (k.val⁻¹.val * A)
  rw [hΦ, hq']

variable {r : ℕ}

local instance squarePolynomialAverageGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance squarePolynomialAverageGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

local notation "M" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "U" => unitaryCompact ℂ (r + 1)
local notation "P" => MvPolynomial (Coordinates (r + 1) (r + 1)) ℂ

/-- Taking a continuous weighted compact average of inverse left translates of a
standard square polynomial Gaussian preserves its form and its degree bound. -/
def ComplexSquareZetaPolynomialAverageStatement : Prop :=
  ∀ (κ : Measure U) [IsFiniteMeasure κ] (u : U → U) (hu : Continuous u)
    (w : U → ℂ) (hw : Continuous w) (Φ : 𝓢(M, ℂ)) (p : P),
    (Φ : M → ℂ) = squarePolynomialGaussian p →
    ∃ q : P, q.totalDegree ≤ p.totalDegree ∧
      (leftAverageInv κ u hu w hw Φ : M → ℂ) = squarePolynomialGaussian q

theorem leftAverageInv_squarePolynomialGaussian : ComplexSquareZetaPolynomialAverageStatement (r := r) := by
  intro κ _ u hu w hw Φ p hΦ
  let V := (restrictTotalDegree (Coordinates (r + 1) (r + 1)) ℂ p.totalDegree).map
    (polynomialGaussianLinear (r + 1))
  let F (k : U) (A : M) := w k * Φ ((u k).val⁻¹.val * A)
  have hF (k : U) : F k ∈ V := by
    obtain ⟨q, hq, hq'⟩ := exists_left_squarePolynomialGaussian p (u k)
    apply Submodule.smul_mem V (w k)
    refine ⟨q, (mem_restrictTotalDegree _ _ _).mpr hq, funext fun A => ?_⟩
    change squarePolynomialGaussian q A = Φ ((u k).val⁻¹.val * A)
    rw [hΦ, hq']
  have hInt (A : M) : Integrable (fun k => F k A) κ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact hw.mul (Φ.continuous.comp
      ((Units.continuous_val.comp (continuous_subtype_val.comp hu).inv).matrix_mul continuous_const))
  obtain ⟨q, hq, he⟩ := InductionStages.integral_mem κ V hF hInt
  refine ⟨q, (mem_restrictTotalDegree _ _ _).mp hq, funext fun A => ?_⟩
  exact (leftAverageInv_apply κ u hu w hw Φ A).trans (congrFun he A).symm

end Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta
