import Langlands.Global.RankinSelberg.ComplexGodementStandardGaussians
import Langlands.Global.RankinSelberg.ComplexStandardGaussianFourier

/-! # Compact finiteness and Fourier inversion for standard split Godement tests -/

noncomputable section

open MvPolynomial Set
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean
open ComplexGodement (translateTest)
open ComplexGodementGaussianPolynomial
open ComplexAdjacentUnfolding (dilateMatrixTest_apply)
open ComplexGodementColumnProduct (columnProduct columnProduct_apply leadingColumns lastColumn)
open ComplexSquareZeta (squarePolynomialGaussian)
open ComplexEqualPolynomialGeneration (IsGaussianPolynomialRow)
open ComplexAdjacentUnfolding (complexAdjacentSplitFourier splitRowTransform splitRowTransform_apply)
open Langlands.GodementJacquet (complexSelfDualMeasure_neg_scale)

local notation "Mat" => fun m n => Matrix (Fin m) (Fin n) ℂ
local notation "scale" => (2 * Real.pi : ℝ)

/-- Each rectangular polynomial Gaussian of standard scale equals a dilated matrix test. -/
theorem exists_standardMatrixTest_of_eq {m n : ℕ} (Φ : 𝓢(Mat m n, ℂ))
    (p : MvPolynomial (Coordinates m n) ℂ)
    (hΦ : ∀ A, Φ A = eval (coordinates A) p * (Real.exp (-scale * matrixSqNorm A) : ℂ)) :
    ∃ q : MvPolynomial (Coordinates m n) ℂ, Φ = standardMatrixTest q := by
  let c : ℂ := Real.sqrt scale
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  let q := bind₁ (fun j : Coordinates m n => C c⁻¹ * X j) p
  refine ⟨q, SchwartzMap.ext fun A => ?_⟩
  rw [hΦ, standardMatrixTest_apply]
  congr 1
  change aeval (coordinates A) p = aeval (coordinates A) (bind₁ (fun j : Coordinates m n => C c * X j) q)
  rw [aeval_bind₁]
  change aeval (coordinates A) p = aeval _ (bind₁ (fun j : Coordinates m n => C c⁻¹ * X j) p)
  rw [aeval_bind₁]
  congr 2
  funext j
  simp only [map_mul, aeval_C, aeval_X, Algebra.algebraMap_self, RingHom.id_apply,
    ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- The standard scalar dilation preserves finite right unitary translate span. -/
theorem finiteDimensional_translateTest_standardMatrixTest {m : ℕ}
    (p : MvPolynomial (Coordinates m (m + 1)) ℂ) :
    FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℂ (m + 1) =>
      translateTest k.val (standardMatrixTest p))) := by
  let T := LinearMap.funLeft ℂ ℂ fun A : Mat m (m + 1) => (standardGaussianDilation : ℂ) • A
  let S := Submodule.span ℂ (range fun k : unitaryCompact ℂ (m + 1) =>
    translateTest k.val (gaussianPolynomial p))
  let : FiniteDimensional ℂ S := finiteDimensional_translateTest_gaussianPolynomial p
  apply Submodule.finiteDimensional_of_le (S₂ := S.map T)
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨k, rfl⟩
  refine ⟨_, Submodule.subset_span ⟨k, rfl⟩, funext fun A => ?_⟩
  change gaussianPolynomial p (((standardGaussianDilation : ℂ) • A) * k.val.val) =
    standardMatrixTest p (A * k.val.val)
  rw [standardMatrixTest, dilateMatrixTest_apply, Matrix.smul_mul]

section PositiveRank

variable {r : ℕ}
local notation "m" => (r + 1 : ℕ)

private theorem columnProduct_standard_polynomial (Φ : 𝓢(Mat m m, ℂ))
    (P : MvPolynomial (Coordinates m m) ℂ) (hΦ : (Φ : Mat m m → ℂ) = squarePolynomialGaussian P)
    (φ : 𝓢(Fin m → ℂ, ℂ)) (hφ : IsGaussianPolynomialRow scale φ) :
    ∃ p : MvPolynomial (Coordinates m (m + 1)) ℂ, columnProduct Φ φ = standardMatrixTest p := by
  obtain ⟨q, hq⟩ := hφ
  let P' := rename (fun j : Coordinates m m => (j.1, j.2.1.castSucc, j.2.2)) P
  let q' := rename (fun j : Fin m × Bool => (j.1, Fin.last m, j.2)) q
  apply exists_standardMatrixTest_of_eq (columnProduct Φ φ) (P' * q')
  intro A
  rw [columnProduct_apply, hΦ, hq]
  change (eval (coordinates (leadingColumns A)) P *
      (Real.exp (-scale * matrixSqNorm (leadingColumns A)) : ℂ)) *
      (eval (fun j : Fin m × Bool => if j.2 then ((lastColumn A j.1).im : ℂ)
        else ((lastColumn A j.1).re : ℂ)) q *
        (Real.exp (-scale * ∑ i, ‖lastColumn A i‖ ^ 2) : ℂ)) = _
  have h₁ : coordinates (leadingColumns A) = fun j : Coordinates m m =>
      coordinates A (j.1, j.2.1.castSucc, j.2.2) := rfl
  have h₂ : ∀ j : Fin m × Bool,
      (if j.2 then ((lastColumn A j.1).im : ℂ) else ((lastColumn A j.1).re : ℂ)) =
        coordinates A (j.1, Fin.last m, j.2) := by
    rintro ⟨i, b⟩
    cases b <;> rfl
  have hN : matrixSqNorm A = matrixSqNorm (leadingColumns A) + ∑ i, ‖lastColumn A i‖ ^ 2 := by
    unfold matrixSqNorm
    simp only [leadingColumns, Matrix.submatrix_apply, id_eq, lastColumn, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => Fin.sum_univ_castSucc (fun j => ‖A i j‖ ^ 2)
  simp only [P', q', map_mul, eval_rename, Function.comp_def, h₁, h₂, hN, mul_add, Real.exp_add,
    Complex.ofReal_mul]
  ring

end PositiveRank

/-- A split test with the standard Gaussian in both factors has finite right unitary
translate span. -/
def ComplexStandardSplitGodementTestStatement : Prop :=
  ∀ (r : ℕ) (Φ : 𝓢(Mat (r + 1) (r + 1), ℂ)) (P : MvPolynomial (Coordinates (r + 1) (r + 1)) ℂ),
    (Φ : Mat (r + 1) (r + 1) → ℂ) = squarePolynomialGaussian P →
    ∀ (φ : 𝓢(Fin (r + 1) → ℂ, ℂ)), IsGaussianPolynomialRow scale φ →
      FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℂ (r + 1 + 1) =>
        translateTest k.val (columnProduct Φ φ)))

theorem complexStandardSplitGodementTest : ComplexStandardSplitGodementTestStatement := by
  intro r Φ P hΦ φ hφ
  obtain ⟨p, hp⟩ := columnProduct_standard_polynomial Φ P hΦ φ hφ
  rw [hp]
  exact finiteDimensional_translateTest_standardMatrixTest p

/-- Inverse split row Fourier transform preserves the standard polynomial Gaussian class at
unit-modulus trace scale. -/
theorem exists_standard_splitRowTransform_preimage {r : ℕ} (a : ℂˣ) (ha : ‖(a : ℂ)‖ = 1)
    (ψ : 𝓢(Fin (r + 1) → ℂ, ℂ)) (hψ : IsGaussianPolynomialRow scale ψ) :
    ∃ φ : 𝓢(Fin (r + 1) → ℂ, ℂ), IsGaussianPolynomialRow scale φ ∧ splitRowTransform a φ = ψ := by
  refine ⟨splitRowTransform (-a) ψ, ComplexTraceFourier.splitRowTransform_isGaussianPolynomialRow
    (-a) (by simpa using ha) ψ hψ, SchwartzMap.ext fun y => ?_⟩
  have h := (complexAdjacentSplitFourier (-a) (0 : 𝓢(Mat (r + 1) (r + 1), ℂ)) ψ).2 y
  rw [neg_neg, complexSelfDualMeasure_neg_scale] at h
  rw [splitRowTransform_apply]
  exact h

end Langlands.Global.RankinSelbergGlobal
