import Langlands.Global.RankinSelberg.ComplexGodementGaussianPolynomial
import Langlands.Global.RankinSelberg.ComplexSquareZetaConvergence
import Langlands.Global.RankinSelberg.ComplexSquareZetaNormalization
import Langlands.Global.RankinSelberg.ComplexTateProductPolynomialGaussian
import Langlands.Representation.Archimedean.RealInductionStagesFamily

/-! # Polynomial normalizations of standard complex square coefficient integrals -/

noncomputable section

open Complex MeasureTheory MvPolynomial
open scoped ComplexConjugate Matrix.Norms.Operator NNReal SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

open Langlands.Archimedean Langlands.LocalFactor.Archimedean
open Langlands.GeneralLinear (UpperEntryPair)
open ComplexGodement (upperTriangularEntries)
open ComplexGodementGaussianPolynomial (Coordinates coordinates coordinates_re coordinates_im
  matrixSqNorm matrixGaussian_mul_unitary gaussianPolynomial_apply exists_gaussianPolynomial_mul_unitary
  matrixGaussian totalDegree_bind₁_le)
open ComplexSquareFourier (upperMarginal upperMarginal_apply)
open ComplexTateProduct (diagonalCoordinates diagonalPolynomialGaussian complexTateProductPolynomialGaussian)

local instance squarePolynomialGLMeasurable (j : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear j ℂ) := borel _
local instance squarePolynomialGLBorel (j : ℕ) :
    BorelSpace (Langlands.GeneralLinear j ℂ) := ⟨rfl⟩

private def weightedPolynomial {I Y : Type*} (c : Y → I → ℂ) (g : Y → ℂ) :
    MvPolynomial I ℂ →ₗ[ℂ] (Y → ℂ) where
  toFun P x := eval (c x) P * g x
  map_add' P Q := by
    funext x
    simp only [map_add, Pi.add_apply, add_mul]
  map_smul' a P := by
    funext x
    simp only [MvPolynomial.smul_eq_C_mul, map_mul, eval_C, Pi.smul_apply, smul_eq_mul,
      RingHom.id_apply, mul_assoc]

variable {n : ℕ}
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "Idx" => Coordinates n n
local notation "Poly" => MvPolynomial Idx ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Off" => UpperEntryPair n
local notation "Row" => Fin n → ℂ
local notation "scale" => (2 * Real.pi : ℝ)

private def squareGaussian (A : Mat) : ℂ := (Real.exp (-scale * matrixSqNorm A) : ℂ)

/-- A polynomial in the real and imaginary matrix entries times the standard square Gaussian. -/
def squarePolynomialGaussian (P : Poly) (A : Mat) : ℂ := eval (coordinates A) P * squareGaussian A

private theorem matrixSqNorm_mul_unitary (A : Mat) (k : K) :
    matrixSqNorm (A * k.val.val) = matrixSqNorm A := by
  have h := matrixGaussian_mul_unitary A k
  unfold matrixGaussian at h
  exact neg_injective (Real.exp_injective (ofReal_injective h))

/-- Taking a weighted compact average preserves the Gaussian scale and the polynomial degree bound. -/
theorem rightAverage_squarePolynomialGaussian (κ : Measure K) [IsFiniteMeasure κ]
    (w : K → ℂ) (hw : Continuous w) (Φ : 𝓢(Mat, ℂ)) (P : Poly)
    (hΦ : (Φ : Mat → ℂ) = squarePolynomialGaussian P) :
    ∃ Q : Poly, Q.totalDegree ≤ P.totalDegree ∧
      (rightAverage κ w hw Φ : Mat → ℂ) = squarePolynomialGaussian Q := by
  let S := restrictTotalDegree Idx ℂ P.totalDegree
  let L : Poly →ₗ[ℂ] (Mat → ℂ) := weightedPolynomial coordinates squareGaussian
  let V := S.map L
  let a (k : K) (A : Mat) := w k * Φ (A * k.val.val)
  have ha (k : K) : a k ∈ V := by
    obtain ⟨Q, hQ, h⟩ := exists_gaussianPolynomial_mul_unitary P k
    apply Submodule.smul_mem V (w k)
    refine ⟨Q, (mem_restrictTotalDegree _ _ _).mpr hQ, ?_⟩
    funext A
    simp only [gaussianPolynomial_apply, matrixGaussian_mul_unitary] at h
    have hG : matrixGaussian A ≠ 0 := ofReal_ne_zero.mpr (Real.exp_pos _).ne'
    have hEval := mul_right_cancel₀ hG (h A)
    change squarePolynomialGaussian Q A = Φ (A * k.val.val)
    simp only [hΦ, squarePolynomialGaussian, hEval, squareGaussian, matrixSqNorm_mul_unitary]
  have hI (A : Mat) : Integrable (fun k => a k A) κ := by
    apply Continuous.integrable_of_hasCompactSupport _ (HasCompactSupport.of_compactSpace _)
    exact hw.mul (Φ.continuous.comp (continuous_const.matrix_mul
      (Units.continuous_val.comp continuous_subtype_val)))
  obtain ⟨Q, hQ, h⟩ := InductionStages.integral_mem κ V ha hI
  exact ⟨Q, (mem_restrictTotalDegree _ _ _).mp hQ, h.symm⟩

private theorem matrixSqNorm_upperTriangularEntries (d : Row) (u : Off → ℂ) :
    matrixSqNorm (upperTriangularEntries d u) = (∑ i, ‖d i‖ ^ 2) + ∑ ij, ‖u ij‖ ^ 2 := by
  have h (i j : Fin n) : ‖upperTriangularEntries d u i j‖ ^ 2 =
      (if h : i < j then ‖u ⟨(i, j), h⟩‖ ^ 2 else 0) + (if i = j then ‖d i‖ ^ 2 else 0) := by
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [upperTriangularEntries, hij, ne_of_lt hij]
    · simp [upperTriangularEntries]
    · simp [upperTriangularEntries, not_lt_of_gt hji, ne_of_gt hji]
  simp only [matrixSqNorm, h, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rw [add_comm]
  congr 1
  let f (ij : Fin n × Fin n) : ℝ := if h : ij.1 < ij.2 then ‖u ⟨ij, h⟩‖ ^ 2 else 0
  calc
    _ = ∑ ij : Fin n × Fin n, f ij := (Fintype.sum_prod_type f).symm
    _ = _ := Finset.sum_congr_set {ij : Fin n × Fin n | ij.1 < ij.2} f (fun ij : Off => ‖u ij‖ ^ 2)
      (fun ij hij => by
        change ij.1 < ij.2 at hij
        exact dite_eq_left hij)
      (fun ij hij => by
        change ¬ ij.1 < ij.2 at hij
        exact dite_eq_right hij)

private def diagRealCoordinate (i : Fin n) (b : Bool) : MvPolynomial (Fin n × Bool) ℂ :=
  if b then (X (i, false) - X (i, true)) * C ((2 * I)⁻¹)
  else (X (i, false) + X (i, true)) * C (2 : ℂ)⁻¹

private theorem totalDegree_diagRealCoordinate (i : Fin n) (b : Bool) :
    (diagRealCoordinate i b).totalDegree ≤ 1 := by
  cases b
  · unfold diagRealCoordinate
    rw [ite_eq_right Bool.false_ne_true]
    refine (totalDegree_mul _ _).trans ?_
    simpa only [totalDegree_C, add_zero, totalDegree_X, max_self] using
      (totalDegree_add (X (i, false) : MvPolynomial (Fin n × Bool) ℂ) (X (i, true)))
  · unfold diagRealCoordinate
    rw [ite_eq_left rfl, sub_eq_add_neg]
    refine (totalDegree_mul _ _).trans ?_
    simp only [totalDegree_C, add_zero]
    exact (totalDegree_add _ _).trans (by simp [totalDegree_X])

private theorem eval_diagRealCoordinate (d : Row) (i : Fin n) (b : Bool) :
    eval (diagonalCoordinates d) (diagRealCoordinate i b) =
      if b then ((d i).im : ℂ) else ((d i).re : ℂ) := by
  have h : d i + conj (d i) = 2 * ((d i).re : ℂ) := by apply Complex.ext <;> simp [two_mul]
  have h' : d i - conj (d i) = 2 * I * ((d i).im : ℂ) := by
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im, two_mul, add_mul]
  have hI : (2 * I : ℂ) ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  cases b
  · simp only [diagRealCoordinate, diagonalCoordinates, Bool.false_eq_true, ite_false, ite_true,
      map_mul, map_add, eval_X, eval_C, h]
    ring
  · simp only [diagRealCoordinate, diagonalCoordinates, ite_true, Bool.false_eq_true, ite_false,
      map_mul, map_sub, eval_X, eval_C, h']
    rw [mul_right_comm, mul_inv_cancel₀ hI, one_mul]

private def sliceVariable (u : Off → ℂ) (i : Idx) : MvPolynomial (Fin n × Bool) ℂ :=
  if hi : i.1 < i.2.1 then
    C (if i.2.2 then ((u ⟨(i.1, i.2.1), hi⟩).im : ℂ) else ((u ⟨(i.1, i.2.1), hi⟩).re : ℂ))
  else if i.1 = i.2.1 then diagRealCoordinate i.1 i.2.2 else 0

private theorem totalDegree_sliceVariable (u : Off → ℂ) (i : Idx) :
    (sliceVariable u i).totalDegree ≤ 1 := by
  unfold sliceVariable
  split_ifs <;> simp only [totalDegree_C, totalDegree_zero, Nat.zero_le, totalDegree_diagRealCoordinate]

private theorem eval_sliceVariable (d : Row) (u : Off → ℂ) (i : Idx) :
    eval (diagonalCoordinates d) (sliceVariable u i) = coordinates (upperTriangularEntries d u) i := by
  obtain ⟨i, j, b⟩ := i
  rcases lt_trichotomy i j with hij | rfl | hji
  · cases b <;> simp [sliceVariable, upperTriangularEntries, hij]
  · cases b <;> simp [sliceVariable, upperTriangularEntries, eval_diagRealCoordinate]
  · cases b <;> simp [sliceVariable, upperTriangularEntries, not_lt_of_gt hji, ne_of_gt hji]

private theorem prod_scalarGaussian (d : Row) :
    (Real.exp (-scale * ∑ j, ‖d j‖ ^ 2) : ℂ) =
      (Real.pi : ℂ) ^ n * ∏ j, Langlands.LocalFactor.ComplexTate.gaussian 0 (d j) := by
  simp only [Langlands.LocalFactor.ComplexTate.gaussian, Int.natAbs_zero, pow_zero,
    ite_eq_left (le_refl (0 : ℤ)), one_mul, Finset.prod_div_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [mul_comm, mul_div_cancel₀ _ (pow_ne_zero _ (ofReal_ne_zero.mpr Real.pi_ne_zero))]
  rw [ofReal_exp, ← Complex.exp_sum]
  congr 1
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

private theorem exists_polynomialGaussian_upperTriangular (P : Poly) (u : Off → ℂ) :
    ∃ Q : MvPolynomial (Fin n × Bool) ℂ, Q.totalDegree ≤ P.totalDegree ∧
      (fun d => squarePolynomialGaussian P (upperTriangularEntries d u)) = diagonalPolynomialGaussian Q := by
  let b : ℂ := (Real.pi : ℂ) ^ n * (Real.exp (-scale * ∑ ij, ‖u ij‖ ^ 2) : ℂ)
  let Q := C b * bind₁ (sliceVariable u) P
  have hQ : Q.totalDegree ≤ P.totalDegree := by
    apply (totalDegree_mul _ _).trans
    rw [totalDegree_C, zero_add]
    exact totalDegree_bind₁_le _ (totalDegree_sliceVariable u) P
  refine ⟨Q, hQ, funext fun d => ?_⟩
  have hP : eval (diagonalCoordinates d) (bind₁ (sliceVariable u) P) =
      eval (coordinates (upperTriangularEntries d u)) P := by
    simpa only [aeval_eq_eval, eval_sliceVariable] using
      aeval_bind₁ (diagonalCoordinates d) (sliceVariable u) P
  simp only [squarePolynomialGaussian, squareGaussian, matrixSqNorm_upperTriangularEntries,
    mul_add, Real.exp_add, ofReal_mul, prod_scalarGaussian, diagonalPolynomialGaussian, Q, map_mul,
    eval_C, hP, b]
  ring

/-- Integration over the strictly upper triangular entries preserves the Gaussian scale and
bounds the degree of the remaining diagonal polynomial by the original matrix degree. -/
theorem upperMarginal_squarePolynomialGaussian (a : ℂˣ) (Φ : 𝓢(Mat, ℂ)) (P : Poly)
    (hΦ : (Φ : Mat → ℂ) = squarePolynomialGaussian P) :
    ∃ Q : MvPolynomial (Fin n × Bool) ℂ, Q.totalDegree ≤ P.totalDegree ∧
      (upperMarginal a Φ : Row → ℂ) = diagonalPolynomialGaussian Q := by
  let S := restrictTotalDegree (Fin n × Bool) ℂ P.totalDegree
  let L := weightedPolynomial diagonalCoordinates (fun d : Row => ∏ j, Langlands.LocalFactor.ComplexTate.gaussian 0 (d j))
  let V := S.map L
  let μ := Measure.pi (fun _ : Off => (ArchimedeanLocal.complexSelfDualMeasure a).measure)
  have hMem (u : Off → ℂ) : (fun d => Φ (upperTriangularEntries d u)) ∈ V := by
    obtain ⟨Q, hQ, h⟩ := exists_polynomialGaussian_upperTriangular P u
    exact ⟨Q, (mem_restrictTotalDegree _ _ _).mpr hQ, by rw [hΦ, h]; rfl⟩
  have hInt (d : Row) : Integrable (fun u : Off → ℂ => Φ (upperTriangularEntries d u)) μ := by
    dsimp only [μ]
    rw [ComplexTraceFourier.product_measure_eq]
    exact (integrable_upperTriangularSlice Φ d).smul_measure_nnreal
  obtain ⟨Q, hQ, h⟩ := InductionStages.integral_mem μ V hMem hInt
  refine ⟨Q, (mem_restrictTotalDegree _ _ _).mp hQ, funext fun d => ?_⟩
  exact (upperMarginal_apply a Φ d).trans (congrFun h d).symm

/-- The standard square Gaussian coefficient integral is its specified standard L-factor
times a polynomial of degree bounded by the test polynomial on a right half-plane. -/
def ComplexSquareZetaPolynomialGaussianStatement : Prop :=
  ∀ (n : ℕ), 0 < n →
    ∀ (μ : Measure (Langlands.GeneralLinear n ℂ)) [μ.IsHaarMeasure]
      (κ : Measure (unitaryCompact ℂ n)) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
      (ds : Fin n → ComplexCharacterData)
      (Φ : 𝓢(Matrix (Fin n) (Fin n) ℂ, ℂ)) (P : MvPolynomial (Coordinates n n) ℂ),
      (Φ : Matrix (Fin n) (Fin n) ℂ → ℂ) = squarePolynomialGaussian P →
      ∀ f : Langlands.GeneralLinear n ℂ → ℂ, f ∈ complexStandardModule n (List.ofFn ds) →
        ∃ (σ : ℝ) (Q : Polynomial ℂ), Q.natDegree ≤ P.totalDegree ∧
          ∀ s : ℂ, σ < s.re → Integrable (zetaKernel Φ f s) μ ∧
            Q.eval s = (complexLFactor (List.ofFn ds)).denominator s * ∫ g, zetaKernel Φ f s g ∂μ

set_option maxHeartbeats 900000 in
theorem complexSquareZetaPolynomialGaussian : ComplexSquareZetaPolynomialGaussianStatement := by
  intro n hn μ _ κ _ _ ds Φ P hΦ f hf
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  let a : ℂˣ := 1
  obtain ⟨H, hH⟩ := ComplexTateProduct.complexTateProductEntireFamily r
  obtain ⟨c, _, hN⟩ := complexSquareZetaNormalization μ κ a H hH
  let w (k : unitaryCompact ℂ (r + 1)) := f k.val
  let hw : Continuous w := hf.1.continuous.comp continuous_subtype_val
  obtain ⟨A, hAdeg, hA⟩ := rightAverage_squarePolynomialGaussian κ w hw Φ P hΦ
  obtain ⟨D, hDdeg, hD⟩ := upperMarginal_squarePolynomialGaussian a (rightAverage κ w hw Φ) A hA
  obtain ⟨R, hRdeg, hR⟩ := complexTateProductPolynomialGaussian (r + 1) H hH
    (diagonalTest κ a Φ f hf.1.continuous) D hD (fun j => (ds j).weight) (fun j => (ds j).exponent)
  obtain ⟨M, hM⟩ := complexSquareZetaConvergence hn ds
  let b : ℝ := ∑ j, |(ds j).exponent.re|
  let q := ((((r + 1 : ℕ) : ℂ) - 1) / 2).re
  let Q := Polynomial.C (c : ℂ) * R
  refine ⟨max (((r + 1 : ℕ) : ℝ) + M + |q|) b, Q,
    (Polynomial.natDegree_C_mul_le _ _).trans (hRdeg.trans (hDdeg.trans hAdeg)), fun s hs => ?_⟩
  have h₁ := (le_max_left _ _).trans_lt hs
  have h₂ := (le_max_right _ _).trans_lt hs
  have hI := hM μ Φ f hf s (by
    rw [Complex.add_re]
    change ((r + 1 : ℕ) : ℝ) + M ≤ s.re + q
    linarith [neg_abs_le q])
  have hpos (j : Fin (r + 1)) : 0 < (s + (ds j).exponent).re := by
    rw [Complex.add_re]
    have hB : |(ds j).exponent.re| ≤ b :=
      Finset.single_le_sum (fun k _ => abs_nonneg (ds k).exponent.re) (Finset.mem_univ j)
    linarith [neg_abs_le (ds j).exponent.re]
  refine ⟨hI, ?_⟩
  simp only [Q, Polynomial.eval_mul, Polynomial.eval_C, ← hR]
  exact (hN ds Φ f hf).2 s hI hpos

end Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta
