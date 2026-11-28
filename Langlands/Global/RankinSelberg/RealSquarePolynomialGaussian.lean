import Langlands.Global.RankinSelberg.RealDiagonalPolynomialGaussian
import Langlands.Global.RankinSelberg.RealGodementGaussianPolynomial
import Langlands.Global.RankinSelberg.RealTriangularMatched
import Langlands.Representation.Archimedean.RealInductionStagesFamily

/-! # Standard polynomial Gaussians on real triangular slices -/

noncomputable section

open Complex MeasureTheory MvPolynomial
open scoped Matrix.Norms.Operator Real SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealSquarePolynomialGaussian

open Langlands.Archimedean Langlands.GeneralLinear
open RealGodementGaussianPolynomial RealSquareFourier
open Langlands.GodementJacquet (realTriangularMarginal realTriangularMarginal_apply)
open ArchimedeanLocal (realSelfDualMeasure)
open ArchimedeanDeterminantTheta (diagonalPolynomialGaussian diagonalPolynomialGaussian_eq_exp)
open ComplexGodementGaussianPolynomial (totalDegree_bind₁_le)

variable {n : ℕ}
local notation "I" => Fin n
local notation "Mat" => Matrix I I ℝ
local notation "Idx" => Coordinates n n
local notation "Off" => UpperEntryPair n
local notation "Row" => I → ℝ
local notation "K" => unitaryCompact ℝ n
local notation "Poly" => MvPolynomial Idx ℂ

/-- A polynomial in the real matrix entries times the standard Gaussian of scale `π`. -/
def squarePolynomialGaussian (P : Poly) (A : Mat) : ℂ :=
  eval (coordinates A) P * (Real.exp (-π * matrixSqNorm A) : ℂ)

/-- The standard polynomial Gaussian as a Schwartz test. -/
def squarePolynomialSchwartz (P : Poly) : 𝓢(Mat, ℂ) :=
  SchwartzMap.smulLeftCLM ℂ (fun A => eval (coordinates A) P) (scaledGaussian n n π Real.pi_pos)

@[simp]
theorem squarePolynomialSchwartz_apply (P : Poly) (A : Mat) :
    squarePolynomialSchwartz P A = squarePolynomialGaussian P A := by
  rw [squarePolynomialSchwartz, SchwartzMap.smulLeftCLM_apply_apply
    (eval_coordinates_hasTemperateGrowth P), smul_eq_mul, scaledGaussian_apply, squarePolynomialGaussian]
  rw [neg_mul]

/-- Right orthogonal translation preserves the scale and degree bound of a standard test. -/
theorem exists_rightTranslate (P : Poly) (k : K) :
    ∃ Q : Poly, Q.totalDegree ≤ P.totalDegree ∧
      ∀ A, squarePolynomialGaussian P (A * k.val.val) = squarePolynomialGaussian Q A := by
  obtain ⟨Q, hQ, hEval⟩ := exists_rightTranslate_gaussianPolynomial P k
  refine ⟨Q, hQ, fun A => ?_⟩
  have h := hEval A
  simp only [gaussianPolynomial_apply, matrixGaussian_mul_orthogonal] at h
  have hP := mul_right_cancel₀ (ofReal_ne_zero.mpr (Real.exp_pos _).ne' : matrixGaussian A ≠ 0) h
  simp only [squarePolynomialGaussian, matrixSqNorm_mul_orthogonal, hP]

private theorem matrixSqNorm_upperTriangularEntries (d : Row) (u : Off → ℝ) :
    matrixSqNorm (upperTriangularEntries d u) = (∑ i, d i ^ 2) + ∑ ij, u ij ^ 2 := by
  have h (i j : I) : upperTriangularEntries d u i j ^ 2 =
      (if h : i < j then u ⟨(i, j), h⟩ ^ 2 else 0) + (if i = j then d i ^ 2 else 0) := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [upperTriangularEntries, hij, ne_of_lt hij]
    · simp [upperTriangularEntries]
    · simp [upperTriangularEntries, not_lt_of_gt hji, ne_of_gt hji]
  simp only [matrixSqNorm, h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [add_comm]
  congr 1
  let f (ij : I × I) : ℝ := if h : ij.1 < ij.2 then u ⟨ij, h⟩ ^ 2 else 0
  calc
    _ = ∑ ij : I × I, f ij := (Fintype.sum_prod_type f).symm
    _ = _ := Finset.sum_congr_set {ij : I × I | ij.1 < ij.2} f (fun ij : Off => u ij ^ 2)
      (fun ij hij => by change ij.1 < ij.2 at hij; exact dite_eq_left hij)
      (fun ij hij => by change ¬ ij.1 < ij.2 at hij; exact dite_eq_right hij)

private def sliceVariable (u : Off → ℝ) (ij : Idx) : MvPolynomial I ℂ :=
  if h : ij.1 < ij.2 then C (u ⟨ij, h⟩ : ℂ) else if ij.1 = ij.2 then X ij.1 else 0

private theorem eval_sliceVariable (d : Row) (u : Off → ℝ) (ij : Idx) :
    eval (fun i => (d i : ℂ)) (sliceVariable u ij) = coordinates (upperTriangularEntries d u) ij := by
  obtain ⟨i, j⟩ := ij
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [sliceVariable, upperTriangularEntries, hij]
  · simp [sliceVariable, upperTriangularEntries]
  · simp [sliceVariable, upperTriangularEntries, not_lt_of_gt hji, ne_of_gt hji]

private theorem exists_polynomial_of_slice (P : Poly) (u : Off → ℝ) :
    ∃ Q : MvPolynomial I ℂ, Q.totalDegree ≤ P.totalDegree ∧
      (fun d => squarePolynomialGaussian P (upperTriangularEntries d u)) = diagonalPolynomialGaussian Q := by
  let c : ℂ := (Real.exp (-π * ∑ ij, u ij ^ 2) : ℂ)
  let Q := C c * bind₁ (sliceVariable u) P
  have hQ : Q.totalDegree ≤ P.totalDegree := by
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, zero_add]
    apply totalDegree_bind₁_le _ _ P
    intro ij
    unfold sliceVariable
    split_ifs <;> simp
  refine ⟨Q, hQ, funext fun d => ?_⟩
  have hP : eval (fun i => (d i : ℂ)) (bind₁ (sliceVariable u) P) =
      eval (coordinates (upperTriangularEntries d u)) P := by
    simpa only [aeval_eq_eval, eval_sliceVariable] using
      aeval_bind₁ (fun i => (d i : ℂ)) (sliceVariable u) P
  rw [diagonalPolynomialGaussian_eq_exp]
  simp only [squarePolynomialGaussian, matrixSqNorm_upperTriangularEntries, mul_add, Real.exp_add,
    ofReal_mul, Q, map_mul, eval_C, hP, c]
  ring

private theorem integrable_upperTriangularSlice (Φ : 𝓢(Mat, ℂ)) (d : Row) :
    Integrable (fun u : Off → ℝ => Φ (upperTriangularEntries d u)) volume := by
  let T : (Off → ℝ) →ₗ[ℝ] Mat :=
    { toFun := upperTriangularEntries 0
      map_add' := fun x y => by
        ext i j
        by_cases h : i < j <;> simp [upperTriangularEntries, h]
      map_smul' := fun c x => by
        ext i j
        by_cases h : i < j <;> simp [upperTriangularEntries, h] }
  have hT : Function.Injective T := by
    intro x y h
    funext ij
    have he := congrArg (fun A : Mat => A ij.1.1 ij.1.2) h
    simpa [T, upperTriangularEntries, ij.2] using he
  let B := T.toContinuousLinearMap
  obtain ⟨C, hC⟩ := B.antilipschitz_of_injective_of_isClosed_range hT
    (B.toLinearMap.range.closed_of_finiteDimensional)
  have hAffine : upperTriangularEntries d = fun u => B u + Matrix.diagonal d := by
    funext u
    ext i j
    by_cases h : i < j
    · simp [B, T, upperTriangularEntries, h, Matrix.diagonal_apply_ne _ (ne_of_lt h)]
    · simp [B, T, upperTriangularEntries, h, Matrix.diagonal_apply]
  have hGrowth : (upperTriangularEntries d).HasTemperateGrowth := by
    rw [hAffine]
    exact B.hasTemperateGrowth.add (Function.HasTemperateGrowth.const _)
  have hAnti : AntilipschitzWith C (upperTriangularEntries d) :=
    hAffine ▸ fun x y => by dsimp only; rw [edist_add_right]; exact hC x y
  exact (SchwartzMap.compCLMOfAntilipschitz ℂ hGrowth hAnti Φ).integrable

/-- The standard square polynomial Gaussian becomes a diagonal polynomial Gaussian after
right orthogonal translation and integration of the strictly upper entries. -/
def RealSquarePolynomialMarginalStatement : Prop :=
  ∀ (r : ℕ) (Φ : 𝓢(Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ, ℂ)) (P : MvPolynomial (Coordinates (r + 1) (r + 1)) ℂ),
    (Φ : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ → ℂ) = squarePolynomialGaussian P →
    ∀ k : unitaryCompact ℝ (r + 1), ∃ Q : MvPolynomial (Fin (r + 1)) ℂ,
      Q.totalDegree ≤ P.totalDegree ∧
      (realTriangularMarginal 1 Φ k : (Fin (r + 1) → ℝ) → ℂ) = diagonalPolynomialGaussian Q

set_option maxHeartbeats 700000 in
theorem realSquarePolynomialMarginal : RealSquarePolynomialMarginalStatement := by
  intro r Φ P hΦ k
  obtain ⟨T, hT, hRot⟩ := exists_rightTranslate P k
  let S := restrictTotalDegree (Fin (r + 1)) ℂ T.totalDegree
  let L : MvPolynomial (Fin (r + 1)) ℂ →ₗ[ℂ] ((Fin (r + 1) → ℝ) → ℂ) :=
    { toFun := diagonalPolynomialGaussian
      map_add' := fun q₁ q₂ => by
        ext d
        simp only [diagonalPolynomialGaussian, map_add, Pi.add_apply, add_mul]
      map_smul' := fun c q => by
        ext d
        simp only [diagonalPolynomialGaussian, Pi.smul_apply, smul_eq_mul, MvPolynomial.smul_eq_C_mul,
          RingHom.id_apply, map_mul, eval_C, mul_assoc] }
  let V := S.map L
  let w (u : UpperEntryPair (r + 1) → ℝ) (d : Fin (r + 1) → ℝ) :=
    squarePolynomialGaussian T (upperTriangularEntries d u)
  have hw (u : UpperEntryPair (r + 1) → ℝ) : w u ∈ V := by
    obtain ⟨Q, hQ, hEval⟩ := exists_polynomial_of_slice T u
    exact ⟨Q, (mem_restrictTotalDegree _ _ _).mpr hQ, hEval.symm⟩
  have hI (d : Fin (r + 1) → ℝ) : Integrable (fun u => w u d) volume := by
    simpa only [w, squarePolynomialSchwartz_apply] using integrable_upperTriangularSlice (squarePolynomialSchwartz T) d
  obtain ⟨Q, hQ, hEval⟩ := InductionStages.integral_mem volume V hw hI
  refine ⟨Q, ((mem_restrictTotalDegree _ _ _).mp hQ).trans hT, funext fun d => ?_⟩
  have hμ : upperEntryProductMeasure (realSelfDualMeasure (1 : ℝˣ)) (r + 1) = volume := by
    simp [upperEntryProductMeasure, realSelfDualMeasure, volume_pi]
  rw [realTriangularMarginal_apply, hμ, hΦ]
  simp_rw [hRot]
  exact (congrFun hEval d).symm

end Langlands.Global.RankinSelbergGlobal.RealSquarePolynomialGaussian
