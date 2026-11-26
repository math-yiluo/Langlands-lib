import Langlands.Analysis.Complex.PolynomialGaussianFourier
import Langlands.Global.RankinSelberg.ComplexAdjacentSplitFourier
import Langlands.Global.RankinSelberg.ComplexEqualPolynomialGeneration
import Langlands.Global.RankinSelberg.ComplexSquareZetaPolynomialGaussian
import Langlands.Representation.GodementJacquet.ComplexFourierPartition

/-! # Fourier closure of the standard polynomial Gaussians -/

noncomputable section

open MeasureTheory MvPolynomial
open scoped FourierTransform Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexTraceFourier

open ArchimedeanLocal Langlands.LocalFactor.Archimedean
open Langlands.GodementJacquet (complexMatrixFourier complexRectangleUncurry complexSelfDualMeasure_neg_scale)
open Langlands.HarmonicAnalysis (UnitaryAdditiveCharacter rectangularPairing rowMeasure)
open Langlands.Analysis.PolynomialGaussianFourier (exists_polynomial_fourier)

variable {ι : Type*} [Fintype ι]

/-- Real and imaginary coordinate evaluations for a finite family of complex numbers. -/
def realCoordinates (x : ι → ℂ) (j : ι × Bool) : ℂ :=
  if j.2 then (x j.1).im else (x j.1).re

private def coordinateVector [DecidableEq ι] (j : ι × Bool) : Coordinates ι :=
  PiLp.single 2 j.1 (if j.2 then Complex.I else 1)

private theorem inner_coordinateVector [DecidableEq ι] (x : Coordinates ι) (j : ι × Bool) :
    Langlands.Analysis.PolynomialGaussianFourier.coordinates coordinateVector x j =
      realCoordinates (coordinates x) j := by
  rcases j with ⟨j, b⟩
  unfold Langlands.Analysis.PolynomialGaussianFourier.coordinates realCoordinates
  rw [PiLp.inner_apply, Finset.sum_eq_single j]
  · rw [coordinateVector, PiLp.single_eq_same, Complex.inner]
    cases b <;> simp [Complex.mul_re, coordinates]
  · intro i _ hi
    rw [coordinateVector, PiLp.single_eq_of_ne _ hi, inner_zero_right]
  · simp

/-- The polynomial test with the complex self-dual Gaussian at unit trace scale. -/
def standardGaussian (p : MvPolynomial (ι × Bool) ℂ) (x : ι → ℂ) : ℂ :=
  eval (realCoordinates x) p * (Real.exp (-(2 * Real.pi) * ∑ i, ‖x i‖ ^ 2) : ℂ)

private def frequencyVariable (a : ℂˣ) (j : ι × Bool) : MvPolynomial (ι × Bool) ℂ :=
    C (realCoordinates (fun _ => starRingEnd ℂ (2 * (a : ℂ))) j) * X (j.1, false) +
      C (realCoordinates (fun _ => starRingEnd ℂ (2 * (a : ℂ) * Complex.I)) j) * X (j.1, true)

private theorem eval_frequencyVariable (a : ℂˣ) (x : ι → ℂ) (j : ι × Bool) :
    eval (realCoordinates x) (frequencyVariable a j) =
      realCoordinates (coordinates (frequency a (coordinates.symm x))) j := by
  rcases j with ⟨j, b⟩
  simp only [frequencyVariable, map_add, map_mul, eval_C, eval_X, realCoordinates]
  change _ = if b then (((starRingEnd ℂ (2 * (a : ℂ) * x j)).im : ℝ) : ℂ) else
    (((starRingEnd ℂ (2 * (a : ℂ) * x j)).re : ℝ) : ℂ)
  cases b <;> simp [Complex.mul_re, Complex.mul_im] <;> ring

private theorem norm_sq_frequency (a : ℂˣ) (ha : ‖(a : ℂ)‖ = 1) (x : ι → ℂ) :
    ‖frequency a (coordinates.symm x)‖ ^ 2 = 4 * ∑ j, ‖x j‖ ^ 2 := by
  rw [PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [frequency_apply, Complex.norm_conj, norm_mul, norm_mul, Complex.norm_two, ha, mul_one]
  change (2 * ‖x j‖) ^ 2 = 4 * ‖x j‖ ^ 2
  ring

/-- At unit modulus of the trace scale, the exact trace transform preserves the standard
polynomial Gaussian class on finitely many complex coordinates. -/
def ComplexStandardGaussianFourierStatement : Prop :=
  ∀ (a : ℂˣ), ‖(a : ℂ)‖ = 1 →
    ∀ (Φ : 𝓢(ι → ℂ, ℂ)) (p : MvPolynomial (ι × Bool) ℂ),
      (∀ x, Φ x = standardGaussian p x) →
        ∃ q : MvPolynomial (ι × Bool) ℂ, ∀ x, transform a Φ x = standardGaussian q x

theorem transform_standardGaussian : ComplexStandardGaussianFourierStatement (ι := ι) := by
  intro a ha Φ p hΦ
  classical
  let Ψ : 𝓢(Coordinates ι, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ coordinates Φ
  have hCoord (x : Coordinates ι) :
      Langlands.Analysis.PolynomialGaussianFourier.coordinates coordinateVector x =
        realCoordinates (coordinates x) := funext (inner_coordinateVector x)
  have hΨ (x : Coordinates ι) : Ψ x = eval
      (Langlands.Analysis.PolynomialGaussianFourier.coordinates coordinateVector x) p *
      Langlands.Analysis.PolynomialGaussianFourier.gaussian (2 * Real.pi) x := by
    change Φ (coordinates x) = _
    rw [hΦ, hCoord, standardGaussian, Langlands.Analysis.PolynomialGaussianFourier.gaussian,
      PiLp.norm_sq_eq_of_L2, neg_mul]
    rfl
  obtain ⟨q, hq⟩ := exists_polynomial_fourier coordinateVector (2 * Real.pi) (by positivity) Ψ p hΨ
  let c : ℂ := (((scale a : ℝ) ^ Fintype.card ι : ℝ) : ℂ)
  refine ⟨C c * bind₁ (frequencyVariable a) q, fun x => ?_⟩
  change ((scale a : ℝ) ^ Fintype.card ι) • (𝓕 Ψ) (frequency a (coordinates.symm x)) = _
  rw [hq, standardGaussian, Langlands.Analysis.PolynomialGaussianFourier.gaussian,
    norm_sq_frequency a ha, map_mul, eval_C, Complex.real_smul, ← mul_assoc]
  rw [hCoord]
  have he : eval (realCoordinates x) (bind₁ (frequencyVariable a) q) =
      eval (realCoordinates (coordinates (frequency a (coordinates.symm x)))) q := by
    simpa only [aeval_eq_eval, eval_frequencyVariable] using
      aeval_bind₁ (realCoordinates x) (frequencyVariable a) q
  rw [he]
  have hExp (y : ℝ) : -(Real.pi ^ 2 / (2 * Real.pi) * (4 * y)) = -(2 * Real.pi) * y := by
    field_simp [Real.pi_ne_zero]
    ring
  rw [hExp]

/-- At trace scales of unit modulus the split row transform preserves the standard row tests. -/
theorem splitRowTransform_isGaussianPolynomialRow {r : ℕ} (a : ℂˣ) (ha : ‖(a : ℂ)‖ = 1)
    (Φ : 𝓢(Fin (r + 1) → ℂ, ℂ))
    (hΦ : ComplexEqualPolynomialGeneration.IsGaussianPolynomialRow (2 * Real.pi) Φ) :
    ComplexEqualPolynomialGeneration.IsGaussianPolynomialRow (2 * Real.pi)
      (ComplexAdjacentUnfolding.splitRowTransform a Φ) := by
  obtain ⟨p, hp⟩ := hΦ
  have hPa : ‖((-a : ℂˣ) : ℂ)‖ = 1 := by simpa using ha
  obtain ⟨q, hq⟩ := transform_standardGaussian (-a) hPa Φ p hp
  refine ⟨q, fun x => ?_⟩
  change _ = standardGaussian q x
  rw [← hq x, ComplexAdjacentUnfolding.splitRowTransform_apply, transform_apply,
    complexSelfDualMeasure_neg_scale]
  unfold ComplexAdjacentUnfolding.splitRowPlus rowMeasure
  apply integral_congr_ae
  filter_upwards with y
  simp only [UnitaryAdditiveCharacter.complex_apply, complexScaledCharacter_apply, Units.val_neg,
    neg_mul, mul_neg, neg_neg, mul_comm (x _) (y _)]

section Square

open ComplexGodementGaussianPolynomial (matrixSqNorm)
open ComplexSquareFourier (matrixTransform matrixTransform_apply)
open ComplexSquareZeta (squarePolynomialGaussian)

variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "Idx" => Fin n × Fin n
local notation "Poly" => MvPolynomial (ComplexGodementGaussianPolynomial.Coordinates n n) ℂ

private theorem standardGaussian_square (p : Poly) (A : Mat) :
    standardGaussian (rename (fun j => ((j.1, j.2.1), j.2.2)) p) (complexRectangleUncurry n n A) =
      squarePolynomialGaussian p A := by
  simp only [standardGaussian, eval_rename, squarePolynomialGaussian]
  have hEval : realCoordinates (complexRectangleUncurry n n A) ∘
      (fun j : ComplexGodementGaussianPolynomial.Coordinates n n => ((j.1, j.2.1), j.2.2)) =
      ComplexGodementGaussianPolynomial.coordinates A := by
    funext j
    obtain ⟨i, k, b⟩ := j
    cases b <;> rfl
  rw [hEval]
  change _ * (Real.exp (-(2 * Real.pi) * ∑ j : Idx, ‖A j.1 j.2‖ ^ 2) : ℂ) =
    eval (ComplexGodementGaussianPolynomial.coordinates A) p *
    (Real.exp (-(2 * Real.pi) * matrixSqNorm A) : ℂ)
  rw [Fintype.sum_prod_type' (fun i j : Fin n => ‖A i j‖ ^ 2)]
  rfl

private theorem matrixTransform_neg_eq (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) (X : Mat) :
    matrixTransform (-a) Φ X = complexMatrixFourier a Φ X := by
  rw [matrixTransform_apply, complexSelfDualMeasure_neg_scale]
  change _ = ∫ Y : Mat, Φ Y * (complexScaledCharacter a).complex (rectangularPairing Y X)
    ∂Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin n => (complexSelfDualMeasure a).measure))
  apply integral_congr_ae
  filter_upwards with Y
  let Y' : Mat := Y
  have hPair : Matrix.trace (Matrix.transpose X * Y') = rectangularPairing Y' X := by
    simp only [rectangularPairing, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.transpose_apply]
    rw [Finset.sum_comm]
    simp only [mul_comm]
  change Φ Y' * (complexScaledCharacter (-a)).complex (-(Matrix.transpose X * Y').trace) =
    Φ Y' * (complexScaledCharacter a).complex (rectangularPairing Y' X)
  rw [hPair]
  simp only [UnitaryAdditiveCharacter.complex_apply, complexScaledCharacter_apply, Units.val_neg,
    neg_mul, mul_neg, neg_neg]

/-- The positive square Fourier transform of a standard square polynomial Gaussian is again
represented by a Schwartz test of the same form at unit modulus of the trace scale. -/
theorem complexMatrixFourier_standardGaussian (a : ℂˣ) (ha : ‖(a : ℂ)‖ = 1)
    (Φ : 𝓢(Mat, ℂ)) (p : Poly) (hΦ : (Φ : Mat → ℂ) = squarePolynomialGaussian p) :
    ∃ (Ψ : 𝓢(Mat, ℂ)) (q : Poly),
      (Ψ : Mat → ℂ) = complexMatrixFourier a Φ ∧ (Ψ : Mat → ℂ) = squarePolynomialGaussian q := by
  let E := complexRectangleUncurry n n
  let H : 𝓢(Idx → ℂ, ℂ) := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ E.symm Φ
  have hH (x : Idx → ℂ) : H x = standardGaussian (rename (fun j => ((j.1, j.2.1), j.2.2)) p) x := by
    obtain ⟨A, rfl⟩ := E.surjective x
    change Φ (E.symm (E A)) = _
    rw [E.symm_apply_apply]
    exact (congrFun hΦ A).trans (standardGaussian_square p A).symm
  obtain ⟨q, hq⟩ := transform_standardGaussian (-a) (by simpa using ha) H _ hH
  let q' : Poly := rename (fun j => (j.1.1, j.1.2, j.2)) q
  refine ⟨matrixTransform (-a) Φ, q', funext (matrixTransform_neg_eq a Φ), funext fun X => ?_⟩
  calc
    matrixTransform (-a) Φ X = transform (-a) H (E X) := rfl
    _ = standardGaussian q (E X) := hq _
    _ = squarePolynomialGaussian q' X := by
      rw [← standardGaussian_square q' X]
      have he : (fun j : Idx × Bool => (((j.1.1, j.1.2), j.2) : Idx × Bool)) = id := by
        funext j
        cases j
        rfl
      simp only [q', rename_rename, Function.comp_def, he, rename_id_apply]
      rfl

end Square

end Langlands.Global.RankinSelbergGlobal.ComplexTraceFourier
