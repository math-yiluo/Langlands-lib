import Langlands.Global.RankinSelberg.ComplexGodementParametric
import Langlands.Group.GL.Transvection
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-! # Derivatives of the continued Godement value along simple roots -/

noncomputable section

open MeasureTheory Set
open scoped Classical Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementRootDerivatives

open Langlands.GeneralLinear (determinant transvectionUnit)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure UnitaryAdditiveCharacter)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter complexScaledCharacter_apply)
open ComplexGodement (characterWeight)
open ComplexGodementAddedCharacter (rightTest rightTest_apply continuedValue)
open ComplexGodementColumnChange (iteratedKernel)
open ComplexGodementParametric (directionalTest hasDerivAt_integral_iteratedKernel_curve)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexLocalWhittakerGauge (logTorus logTorus_val)
open ArchimedeanLocal (complexNormalizedAbs)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "Square" => Matrix (Fin (r + 1 + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ

private def rootMatrix (a : ℂˣ) (i : Fin (r + 1)) : Square :=
  Matrix.single i.castSucc i.succ ((a⁻¹ : ℂˣ) : ℂ)

/-- Real simple-root transvection scaled by the inverse trace-character parameter. -/
def rootPath (a : ℂˣ) (i : Fin (r + 1)) (t : ℝ) : G' :=
  transvectionUnit i.castSucc i.succ (ne_of_lt Fin.castSucc_lt_succ) ((t : ℂ) * ((a⁻¹ : ℂˣ) : ℂ))

@[simp]
theorem rootPath_val (a : ℂˣ) (i : Fin (r + 1)) (t : ℝ) :
    (rootPath a i t).val = 1 + t • rootMatrix a i := by
  change 1 + Matrix.single i.castSucc i.succ ((t : ℂ) * ((a⁻¹ : ℂˣ) : ℂ)) = _
  rw [rootMatrix, Matrix.smul_single, Complex.real_smul]

@[simp]
theorem rootPath_zero (a : ℂˣ) (i : Fin (r + 1)) : rootPath a i 0 = 1 := by
  apply Units.ext
  simp

private theorem rootPath_inv (a : ℂˣ) (i : Fin (r + 1)) (t : ℝ) : (rootPath a i t)⁻¹ = rootPath a i (-t) := by
  apply Units.ext
  change Matrix.transvection i.castSucc i.succ (-((t : ℂ) * ((a⁻¹ : ℂˣ) : ℂ))) = _
  simp only [rootPath, transvectionUnit, Complex.ofReal_neg, neg_mul]

private theorem continuous_rootPath (a : ℂˣ) (i : Fin (r + 1)) : Continuous (rootPath a i) := by
  apply Units.continuous_iff.mpr
  constructor
  · change Continuous (fun t : ℝ => (rootPath a i t).val)
    simp only [rootPath_val]
    exact continuous_const.add (continuous_id.smul continuous_const)
  · change Continuous (fun t : ℝ => (rootPath a i t)⁻¹.val)
    simp only [rootPath_inv, rootPath_val]
    exact continuous_const.add (continuous_neg.smul continuous_const)

theorem rootPath_mem (a : ℂˣ) (i : Fin (r + 1)) (t : ℝ) :
    rootPath a i t ∈ Langlands.GeneralLinear.upperUnipotent (r + 1 + 1) ℂ := by
  constructor
  · intro p q hpq
    change q < p at hpq
    change (rootPath a i t).val p q = 0
    rw [rootPath_val, Matrix.add_apply, Matrix.one_apply_ne (ne_of_gt hpq), zero_add,
      Matrix.smul_apply, rootMatrix, Matrix.single_apply, ite_eq_right]
    · simp
    · rintro ⟨rfl, rfl⟩
      exact (not_lt_of_ge Fin.castSucc_lt_succ.le) hpq
  · intro p
    change (rootPath a i t).val p p = 1
    rw [rootPath_val, Matrix.add_apply, Matrix.one_apply_eq, Matrix.smul_apply,
      rootMatrix, Matrix.single_apply, ite_eq_right]
    · simp
    · rintro ⟨rfl, he⟩
      exact (ne_of_gt Fin.castSucc_lt_succ) he

private theorem determinant_rootPath (a : ℂˣ) (i : Fin (r + 1)) (t : ℝ) : determinant (rootPath a i t) = 1 := by
  apply Units.ext
  exact Langlands.RankinSelberg.unipotent_det ⟨rootPath a i t, rootPath_mem a i t⟩

/-- The torus conjugation multiplier for an adjacent upper root. -/
def rootRatio (y : Fin (r + 1 + 1) → ℝ) (i : Fin (r + 1)) : ℝ := Real.exp (y i.castSucc - y i.succ)

theorem logTorus_mul_rootPath (a : ℂˣ) (y : Fin (r + 1 + 1) → ℝ) (i : Fin (r + 1)) (t : ℝ) :
    logTorus y * rootPath a i t = rootPath a i (rootRatio y i * t) * logTorus y := by
  apply Units.ext
  simp only [Units.val_mul, rootPath_val, logTorus_val, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul]
  congr 1
  ext p q
  rw [Matrix.diagonal_mul, Matrix.mul_diagonal]
  simp only [Matrix.smul_apply, rootMatrix, Matrix.single_apply]
  by_cases h : i.castSucc = p ∧ i.succ = q
  · obtain ⟨rfl, rfl⟩ := h
    simp only [and_self, ite_true, Complex.real_smul]
    have hρ : rootRatio y i * Real.exp (y i.succ) = Real.exp (y i.castSucc) := by
      rw [rootRatio, ← Real.exp_add, sub_add_cancel]
    have hρc := congrArg (fun x : ℝ => (x : ℂ)) hρ
    push_cast at hρc ⊢
    linear_combination -((t : ℂ) * (a : ℂ)⁻¹) * hρc
  · simp [h]

/-- The constant in the derivative of the left Whittaker character along the scaled root. -/
def rootFrequency : ℂ := ((-4 * Real.pi : ℝ) : ℂ) * Complex.I

theorem rootFrequency_ne_zero : rootFrequency ≠ 0 := by
  unfold rootFrequency
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr (mul_ne_zero (by norm_num) Real.pi_ne_zero)) Complex.I_ne_zero

theorem whittakerCharacter_rootPath (a : ℂˣ) (i : Fin (r + 1)) (t : ℝ) :
    complexWhittakerCharacter (r := r + 1) (-a) (rootPath a i t) = Complex.exp (rootFrequency * (t : ℂ)) := by
  have hs : ∑ j : Fin (r + 1), (rootPath a i t).val j.castSucc j.succ = (t : ℂ) * ((a⁻¹ : ℂˣ) : ℂ) := by
    rw [Finset.sum_eq_single i]
    · simp [rootPath_val, rootMatrix, Matrix.one_apply_ne (ne_of_lt Fin.castSucc_lt_succ), Complex.real_smul]
    · intro j _ hji
      simp [rootPath_val, rootMatrix, Matrix.one_apply_ne (ne_of_lt Fin.castSucc_lt_succ),
        Ne.symm hji]
    · simp
  unfold complexWhittakerCharacter
  rw [hs, UnitaryAdditiveCharacter.complex_apply, complexScaledCharacter_apply]
  simp only [Units.val_neg]
  rw [show -(a : ℂ) * ((t : ℂ) * ((a⁻¹ : ℂˣ) : ℂ)) = -(t : ℂ) by
      calc
        _ = -(t : ℂ) * ((a : ℂ) * ((a⁻¹ : ℂˣ) : ℂ)) := by ring
        _ = -(t : ℂ) := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one],
    ← Complex.ofReal_neg, Algebra.trace_complex_apply, Complex.ofReal_re, Real.fourierChar_apply]
  congr 1
  unfold rootFrequency
  push_cast
  ring

private def rootField (a : ℂˣ) (i : Fin (r + 1)) : Rect →L[ℝ] Rect :=
  (mulRightLinearMap (Fin (r + 1)) ℝ (rootMatrix a i)).toContinuousLinearMap

/-- The test derivative induced by the simple-root path. -/
def rootTestDerivative (a : ℂˣ) (i : Fin (r + 1)) : 𝓢(Rect, ℂ) →L[ℝ] 𝓢(Rect, ℂ) :=
  directionalTest (rootField a i)

private theorem hasDerivAt_mul_rootPath (a : ℂˣ) (i : Fin (r + 1)) (b : G') (t : ℝ) (Y : Rect) :
    HasDerivAt (fun v => Y * (b * rootPath a i v).val) (rootField a i (Y * (b * rootPath a i t).val)) t := by
  let A := rootMatrix a i
  have hA : A * A = 0 := by
    simp [A, rootMatrix, ne_of_gt Fin.castSucc_lt_succ]
  have he (v : ℝ) : Y * (b * rootPath a i v).val = Y * b.val + v • (Y * b.val * A) := by
    rw [Units.val_mul, ← Matrix.mul_assoc, rootPath_val, Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul]
  have hfield : rootField a i (Y * (b * rootPath a i t).val) = Y * b.val * A := by
    change (Y * (b * rootPath a i t).val) * A = _
    rw [he, Matrix.add_mul, Matrix.smul_mul, Matrix.mul_assoc (Y * b.val), hA, Matrix.mul_zero, smul_zero, add_zero]
  rw [hfield]
  simp_rw [he]
  simpa only [one_smul] using ((hasDerivAt_id' t).smul_const (Y * b.val * A)).const_add (Y * b.val)

/-- The fixed determinant factor outside the outer integral of a continued Godement value. -/
def determinantFactor (d : ComplexCharacterData) (g : G') (s : ℂ) : ℂ :=
  ((d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) * characterWeight d (((r + 1 : ℕ) : ℂ) / 2) (determinant g)) *
    ArchimedeanLocal.detPower complexNormalizedAbs g s

private theorem determinantFactor_path (d : ComplexCharacterData) (a : ℂˣ) (i : Fin (r + 1))
    (b k : G') (t : ℝ) (s : ℂ) : determinantFactor d (b * rootPath a i t * k) s = determinantFactor d (b * k) s := by
  have hdet : determinant (b * rootPath a i t * k) = determinant (b * k) := by
    simp only [map_mul, determinant_rootPath, mul_one]
  have hv : (b * rootPath a i t * k).val.det = (b * k).val.det :=
    congrArg (fun z : ℂˣ => (z : ℂ)) hdet
  unfold determinantFactor ArchimedeanLocal.detPower
  rw [hdet, hv]

private theorem rightTest_path (a : ℂˣ) (i : Fin (r + 1)) (b k : G') (t : ℝ) (Φ : 𝓢(Rect, ℂ)) :
    rightTest (b * rootPath a i t * k) Φ = rightTest (b * rootPath a i t) (rightTest k Φ) := by
  ext X
  simp only [rightTest_apply, Units.val_mul, Matrix.mul_assoc]

/-- All simple-root derivatives of a continued Godement test along a torus-unitary slice
are the same outer integral applied to the corresponding differentiated test. -/
theorem iteratedDeriv_continuedValue_rootPath {P : Type} (ν : Measure G) [ν.IsHaarMeasure]
    (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (d : ComplexCharacterData) (S : Set P) (W : P → G → ℂ)
    (hWc : ∀ p ∈ S, Continuous (W p)) (hWb : HasUniformSimpleRootBound S W)
    (p : P) (hp : p ∈ S) (Φ : 𝓢(Rect, ℂ)) (s : ℂ) (i : Fin (r + 1)) (b k : G') (J : ℕ) (t : ℝ) :
    iteratedDeriv J (fun v => continuedValue ν μ d a Φ (W p) (b * rootPath a i v * k) s) t =
      determinantFactor d (b * k) s *
        ∫ h, iteratedKernel (complexScaledCharacter a) μ d
          (rightTest (b * rootPath a i t) ((rootTestDerivative a i ^ J) (rightTest k Φ))) (W p)
          ((((r + 1 : ℕ) + 1 : ℂ) / 2) + s) h ∂ν := by
  let C := determinantFactor d (b * k) s
  let v (t : ℝ) := b * rootPath a i t
  let z := (((r + 1 : ℕ) + 1 : ℂ) / 2) + s
  let f (Ψ : 𝓢(Rect, ℂ)) (t : ℝ) :=
    ∫ h, iteratedKernel (complexScaledCharacter a) μ d (rightTest (v t) Ψ) (W p) z h ∂ν
  have hD (Ψ : 𝓢(Rect, ℂ)) (t : ℝ) : HasDerivAt (f Ψ) (f (rootTestDerivative a i Ψ) t) t :=
    hasDerivAt_integral_iteratedKernel_curve ν μ a d S W hWc hWb p hp Ψ z v
      ((continuous_rootPath a i).const_mul b) (rootField a i) (hasDerivAt_mul_rootPath a i b) t
  have he (t : ℝ) : continuedValue ν μ d a Φ (W p) (b * rootPath a i t * k) s = C * f (rightTest k Φ) t := by
    change determinantFactor d (b * rootPath a i t * k) s *
      (∫ h, iteratedKernel (complexScaledCharacter a) μ d (rightTest (b * rootPath a i t * k) Φ) (W p) z h ∂ν) = _
    rw [determinantFactor_path, rightTest_path]
  simp_rw [he]
  induction J generalizing t with
  | zero => simp [C, f, v, z]
  | succ J ih =>
    rw [iteratedDeriv_succ, funext ih]
    have hd := ((hD ((rootTestDerivative a i ^ J) (rightTest k Φ)) t).const_mul C).deriv
    simpa only [C, f, v, z, pow_succ', mul_apply_eq_comp] using hd

/-- The iterated derivative at zero of the character on a real root line. -/
theorem iteratedDeriv_exp_linear_zero (ω z : ℂ) (J : ℕ) :
    iteratedDeriv J (fun t : ℝ => Complex.exp (ω * (t : ℂ)) * z) 0 = ω ^ J * z := by
  have he (t : ℝ) : HasDerivAt (fun v : ℝ => Complex.exp (ω * (v : ℂ)))
      (Complex.exp (ω * (t : ℂ)) * ω) t := by
    have h : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 t := Complex.ofRealCLM.hasFDerivAt.hasDerivAt
    simpa only [mul_one] using (h.const_mul ω).cexp
  have h (t : ℝ) : iteratedDeriv J (fun v : ℝ => Complex.exp (ω * (v : ℂ)) * z) t =
      Complex.exp (ω * (t : ℂ)) * (ω ^ J * z) := by
    induction J generalizing t with
    | zero => simp
    | succ J ih =>
      rw [iteratedDeriv_succ, funext ih, ((he t).mul_const _).deriv, pow_succ]
      ring
  simpa only [Complex.ofReal_zero, mul_zero, Complex.exp_zero, one_mul] using h 0

variable (r) in
/-- Differentiating the continued Godement value on a simple-root line replaces the test by
the corresponding iterated linear-vector-field derivative. -/
def ComplexGodementRootDerivativesStatement : Prop :=
  ∀ {P : Type} (ν : Measure G) [ν.IsHaarMeasure] (μ : AdditiveHaarMeasure ℂ)
    (a : ℂˣ) (d : ComplexCharacterData) (S : Set P) (W : P → G → ℂ),
    (∀ p ∈ S, Continuous (W p)) → HasUniformSimpleRootBound S W →
    ∀ p ∈ S, ∀ (Φ : 𝓢(Rect, ℂ)) (s : ℂ) (i : Fin (r + 1)) (b k : G') (J : ℕ) (t : ℝ),
      iteratedDeriv J (fun v => continuedValue ν μ d a Φ (W p) (b * rootPath a i v * k) s) t =
        determinantFactor d (b * k) s *
          ∫ h, iteratedKernel (complexScaledCharacter a) μ d
            (rightTest (b * rootPath a i t) ((rootTestDerivative a i ^ J) (rightTest k Φ))) (W p)
            ((((r + 1 : ℕ) + 1 : ℂ) / 2) + s) h ∂ν

theorem complexGodementRootDerivatives : ComplexGodementRootDerivativesStatement r := by
  intro P ν hν μ a d S W hWc hWb p hp Φ s i b k J t
  exact iteratedDeriv_continuedValue_rootPath ν μ a d S W hWc hWb p hp Φ s i b k J t

end Langlands.Global.RankinSelbergGlobal.ComplexGodementRootDerivatives
