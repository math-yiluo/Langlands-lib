import Langlands.Analysis.GaussianWeightedMoment
import Langlands.Global.RankinSelberg.ComplexGodementGaussianPolynomial
import Langlands.Global.RankinSelberg.ComplexGodementHalfGaussian
import Langlands.Representation.Archimedean.ComplexDuality.UnitaryHaar
import Mathlib.LinearAlgebra.Matrix.Bilinear

/-! # Gaussian moment detection for the compact Godement pairings -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap Langlands.Archimedean.ComplexDuality

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open ComplexGodementFourier (curryLinearEquiv)
open ComplexGodementGaussianPolynomial (Coordinates coordinates coordinates_re coordinates_im
  eval_hasTemperateGrowth gaussianPolynomial gaussianPolynomial_apply matrixGaussian matrixSqNorm)
open Langlands.Analysis.GaussianWeightedMoment
  (integrable_mul_of_hasCompactSupport integral_eq_zero_of_gaussian_moments)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel

section Polynomial

variable {m n : ℕ}

local notation "Mat" => Matrix (Fin m) (Fin n) ℂ
local notation "Poly" => MvPolynomial (Coordinates m n) ℂ

private def coordinateLinear (v : Coordinates m n) : Mat →ₗ[ℝ] ℝ :=
  let entry : Mat →ₗ[ℝ] ℂ :=
    { toFun A := A v.1 v.2.1
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  (if v.2.2 then Complex.imCLM.toLinearMap else Complex.reCLM.toLinearMap).comp entry

private theorem ofReal_coordinateLinear (v : Coordinates m n) (A : Mat) :
    (coordinateLinear v A : ℂ) = coordinates A v := by
  rcases v with ⟨i, j, b⟩
  cases b <;> rfl

/-- Encode a real linear functional on matrices as a polynomial in real entry coordinates. -/
def realLinearPolynomial (L : Mat →ₗ[ℝ] ℝ) : Poly :=
  ∑ i, ∑ j,
    (MvPolynomial.C (L (Matrix.single i j 1) : ℂ) * MvPolynomial.X (i, j, false) +
      MvPolynomial.C (L (Matrix.single i j Complex.I) : ℂ) * MvPolynomial.X (i, j, true))

theorem eval_realLinearPolynomial (L : Mat →ₗ[ℝ] ℝ) (A : Mat) :
    MvPolynomial.eval (coordinates A) (realLinearPolynomial L) = (L A : ℂ) := by
  have hsum : (∑ i, ∑ j, ((A i j).re • Matrix.single i j (1 : ℂ) +
      (A i j).im • Matrix.single i j Complex.I)) = A := by
    refine (Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_).trans
      (Matrix.sum_sum_single A)
    rw [Matrix.smul_single, Matrix.smul_single, ← Matrix.single_add]
    simp only [Complex.real_smul, mul_one, Complex.re_add_im]
  conv_rhs => rw [← hsum]
  simp only [realLinearPolynomial, map_sum, map_add, map_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, coordinates_re, coordinates_im, map_smul, smul_eq_mul,
    Complex.ofReal_sum, Complex.ofReal_add, Complex.ofReal_mul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm (L (Matrix.single i j 1) : ℂ), mul_comm (L (Matrix.single i j Complex.I) : ℂ)]

/-- Right multiplication by a unitary preserves the class of polynomial Gaussian tests. -/
theorem exists_rightTranslate_gaussianPolynomial (P : Poly) (k : unitaryCompact ℂ n) :
    ∃ Q : Poly, ∀ A : Mat, gaussianPolynomial P (A * k.val.val) = gaussianPolynomial Q A := by
  let L (v : Coordinates m n) :=
    (coordinateLinear v).comp (mulRightLinearMap (Fin m) ℝ k.val.val)
  let q (v : Coordinates m n) := realLinearPolynomial (L v)
  refine ⟨MvPolynomial.bind₁ q P, fun A => ?_⟩
  rw [gaussianPolynomial_apply, gaussianPolynomial_apply,
    ComplexGodementGaussianPolynomial.matrixGaussian_mul_unitary]
  congr 1
  change MvPolynomial.aeval (coordinates (A * k.val.val)) P =
    MvPolynomial.aeval (coordinates A) (MvPolynomial.bind₁ q P)
  rw [MvPolynomial.aeval_bind₁]
  have hq (v : Coordinates m n) :
      MvPolynomial.aeval (coordinates A) (q v) = coordinates (A * k.val.val) v :=
    (eval_realLinearPolynomial (L v) A).trans (ofReal_coordinateLinear v _)
  simp_rw [hq]

private theorem exists_gaussianPolynomial_half_factor (P : Poly) :
    ∃ Ψ : 𝓢(Mat, ℂ), ∀ A : Mat,
      gaussianPolynomial P A = Ψ A * godementHalfGaussian m n A := by
  let coord (v : Coordinates m n) : Mat →L[ℝ] ℂ :=
    Complex.ofRealCLM.comp (coordinateLinear v).toContinuousLinearMap
  have hcoord (A : Mat) (v : Coordinates m n) : coord v A = coordinates A v :=
    ofReal_coordinateLinear v A
  have hg : (fun A : Mat => MvPolynomial.eval (coordinates A) P).HasTemperateGrowth := by
    simpa only [hcoord] using eval_hasTemperateGrowth coord P
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun A : Mat => MvPolynomial.eval (coordinates A) P)
    (godementHalfGaussian m n), fun A => ?_⟩
  rw [gaussianPolynomial_apply, SchwartzMap.smulLeftCLM_apply_apply hg]
  simp only [smul_eq_mul, godementHalfGaussian_apply, matrixGaussian, matrixSqNorm,
    mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add]
  apply congrArg (fun s : ℝ => MvPolynomial.eval (coordinates A) P * (Real.exp s : ℂ))
  ring

end Polynomial

variable {r : ℕ}

local notation "m" => (r + 1 : ℕ)
local notation "H" => Langlands.GeneralLinear (r + 1) ℂ
local notation "U" => unitaryCompact ℂ (r + 1 + 1)
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Poly" => MvPolynomial (Coordinates (r + 1) (r + 1 + 1)) ℂ
local notation "E" => EuclideanSpace ℂ (Fin (r + 1) × Fin (r + 1 + 1))

private def euclidean : Rect ≃L[ℝ] E :=
  ((curryLinearEquiv (Fin (r + 1)) (Fin (r + 1 + 1)) ℝ ℂ).symm.trans
    (WithLp.linearEquiv 2 ℝ (Fin (r + 1) × Fin (r + 1 + 1) → ℂ)).symm).toContinuousLinearEquiv

private theorem euclidean_norm_sq (A : Rect) : ‖euclidean A‖ ^ 2 = matrixSqNorm A := by
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
  rfl

private def compactSample (x : U × H) : Rect :=
  x.2.val * trailingRows x.1.val.val

private theorem continuous_compactSample : Continuous (compactSample (r := r)) := by
  exact (Units.continuous_val.comp continuous_snd).matrix_mul
    (((Units.continuous_val.comp continuous_subtype_val).comp continuous_fst).matrix_submatrix _ _)

private def pairingWeight (d : ComplexCharacterData) (w : U → ℂ) : U → ℂ :=
  fun k => w k * characterWeight d ((m : ℂ) / 2) (determinant k.val)

private theorem continuous_pairingWeight (d : ComplexCharacterData) {w : U → ℂ} (hw : Continuous w) :
    Continuous (pairingWeight d w) :=
  hw.mul ((continuous_characterWeight d _).comp (determinantContinuous.continuous.comp continuous_subtype_val))

private def jointWeight (d : ComplexCharacterData) (f : H → ℂ) (w : U → ℂ) : U × H → ℂ :=
  fun x => pairingWeight d w x.1 * (f x.2⁻¹ * characterWeight d (((m : ℂ) + 1) / 2) (determinant x.2))

private theorem continuous_jointWeight (d : ComplexCharacterData) {f : H → ℂ} (hf : Continuous f)
    {w : U → ℂ} (hw : Continuous w) : Continuous (jointWeight d f w) :=
  ((continuous_pairingWeight d hw).comp continuous_fst).mul <|
    (hf.comp continuous_snd.inv).mul ((continuous_characterWeight d _).comp
      (determinantContinuous.continuous.comp continuous_snd))

private theorem compact_pairing_product (ν : Measure H) [SFinite ν] (μ : Measure U) [SFinite μ]
    (d : ComplexCharacterData) (f : H → ℂ) (w : U → ℂ) (Φ : Rect → ℂ)
    (h : Integrable (fun x => Φ (compactSample x) * jointWeight d f w x) (μ.prod ν)) :
    Integrable (fun k => w k * godementSection ν d Φ f k.val) μ ∧
    (∫ k, w k * godementSection ν d Φ f k.val ∂μ) =
      ∫ x, Φ (compactSample x) * jointWeight d f w x ∂μ.prod ν := by
  have hp (k : U) :
      (∫ y, Φ (compactSample (k, y)) * jointWeight d f w (k, y) ∂ν) =
        w k * godementSection ν d Φ f k.val := by
    have hk (y : H) : Φ (compactSample (k, y)) * jointWeight d f w (k, y) =
        pairingWeight d w k * godementSectionIntegrand d Φ f k.val y := by
      simp only [compactSample, jointWeight, godementSectionIntegrand]
      ring
    simp only [hk, integral_const_mul, pairingWeight, godementSection, mul_assoc]
  refine ⟨h.integral_prod_left.congr (ae_of_all _ hp), ?_⟩
  rw [integral_prod _ h]
  simp only [hp]

/-- In the standard Godement convergence half-plane, the polynomial Gaussian
sections pair integrably with continuous compact weights. Every such weight
annihilating those sections also annihilates the sections of compact Schwartz tests. -/
def ComplexGodementGaussianPairingStatement : Prop :=
  ∀ (ν : Measure H) [ν.IsHaarMeasure] (ds : List ComplexCharacterData), ds.length = m →
    ∃ M : ℕ, ∀ (d : ComplexCharacterData) (f : H → ℂ), f ∈ complexStandardModule m ds →
    (m : ℝ) + M ≤ (d.exponent + (((m : ℂ) + 1) / 2)).re →
    ∀ (μ : Measure U) [IsFiniteMeasure μ] (w : U → ℂ), Continuous w →
      (∀ P : Poly, Integrable (fun k => w k * godementSection ν d (gaussianPolynomial P) f k.val) μ) ∧
      ((∀ P : Poly, (∫ k, w k * godementSection ν d (gaussianPolynomial P) f k.val ∂μ) = 0) →
        ∀ Φ : 𝓢(Rect, ℂ), HasCompactSupport Φ →
          (∫ k, w k * godementSection ν d Φ f k.val ∂μ) = 0)

theorem complexGodementGaussianPairing : ComplexGodementGaussianPairingStatement (r := r) := by
  intro ν hν ds hlen
  let eH := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) m
  let : LocallyCompactSpace H := eH.locallyCompactSpace
  let : SecondCountableTopology H := eH.secondCountableTopology
  obtain ⟨M, hM⟩ := complexGodementHalfGaussian.{0} (r := r) ν ds hlen
  refine ⟨M, fun d f hf hd μ _ w hw => ?_⟩
  let W := jointWeight d f w
  let φ := godementHalfGaussian m (m + 1)
  let p := euclidean ∘ compactSample (r := r)
  have hW : Measurable W := (continuous_jointWeight d hf.1.continuous hw).measurable
  have hp : Measurable p := (euclidean.continuous.comp continuous_compactSample).measurable
  have hw₁ : Integrable (pairingWeight d w) μ :=
    (continuous_pairingWeight d hw).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hhalf : Integrable (fun x => φ (compactSample x) * W x) (μ.prod ν) := by
    refine (hM d f hf hd U μ (pairingWeight d w) hw₁ id).congr (ae_of_all _ fun x => ?_)
    change pairingWeight d w x.1 * godementSectionIntegrand d φ f x.1.val x.2 =
      φ (compactSample x) * W x
    simp only [W, jointWeight, compactSample, godementSectionIntegrand]
    ring
  have hhalfE : Integrable (fun x => (Real.exp (-‖p x‖ ^ 2 / 2) : ℂ) * W x) (μ.prod ν) := by
    simpa only [p, Function.comp_apply, euclidean_norm_sq, matrixSqNorm, φ, godementHalfGaussian_apply]
      using hhalf
  have hP (P : Poly) :
      Integrable (fun x => gaussianPolynomial P (compactSample x) * W x) (μ.prod ν) := by
    obtain ⟨Ψ, hΨ⟩ := exists_gaussianPolynomial_half_factor P
    have hΨc := Ψ.continuous.comp continuous_compactSample
    have hb := ae_of_all (μ.prod ν) (fun x : U × H =>
      Ψ.norm_le_seminorm ℝ (compactSample x))
    refine (hhalf.bdd_mul hΨc.aestronglyMeasurable hb).congr (ae_of_all _ fun x => ?_)
    change Ψ (compactSample x) * (godementHalfGaussian m (m + 1) (compactSample x) * W x) =
      gaussianPolynomial P (compactSample x) * W x
    rw [hΨ, ← mul_assoc]
  refine ⟨fun P => (compact_pairing_product ν μ d f w _ (hP P)).1, fun hzero Φ hΦc => ?_⟩
  let F : E → ℂ := Φ ∘ euclidean.symm
  have hF : Measurable F := (Φ.continuous.comp euclidean.symm.continuous).measurable
  have hFi := integrable_mul_of_hasCompactSupport hp hW hhalfE hF
    (hΦc.comp_homeomorph euclidean.symm.toHomeomorph)
    ⟨SchwartzMap.seminorm ℝ 0 0 Φ, fun X => Φ.norm_le_seminorm ℝ (euclidean.symm X)⟩
  have hΦi : Integrable (fun x => Φ (compactSample x) * W x) (μ.prod ν) := by
    simpa only [F, p, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using hFi
  rw [(compact_pairing_product ν μ d f w Φ hΦi).2]
  have hmot (L : E →L[ℝ] ℝ) (j : ℕ) :
      (∫ x, (L (p x) : ℂ) ^ j * ((Real.exp (-‖p x‖ ^ 2) : ℂ) * W x) ∂μ.prod ν) = 0 := by
    let P := (realLinearPolynomial (L.toLinearMap.comp euclidean.toLinearEquiv.toLinearMap)) ^ j
    have heq (x : U × H) :
        (L (p x) : ℂ) ^ j * ((Real.exp (-‖p x‖ ^ 2) : ℂ) * W x) =
          gaussianPolynomial P (compactSample x) * W x := by
      simp only [P, gaussianPolynomial_apply, map_pow, eval_realLinearPolynomial,
        LinearMap.comp_apply, ContinuousLinearEquiv.coe_toLinearEquiv, LinearEquiv.coe_coe,
        ContinuousLinearMap.coe_coe, matrixGaussian, p, Function.comp_apply, euclidean_norm_sq,
        mul_assoc]
    simp_rw [heq]
    exact (compact_pairing_product ν μ d f w _ (hP P)).2.symm.trans (hzero P)
  simpa only [F, p, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply] using
    integral_eq_zero_of_gaussian_moments hp hW hhalfE hmot hF hFi

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
