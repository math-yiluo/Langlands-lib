import Langlands.Global.RankinSelberg.RealMatrixContinuation

/-! # Transport of real matrix theta identities to arbitrary evaluation points -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear
open Langlands.Archimedean.RealJacquetFrobenius (charFun)
open Langlands.Global.RankinSelbergGlobal
open ArchimedeanLocal ArchimedeanMellinPair ArchimedeanDeterminantTheta RealSquareFourier RealGodement

local instance realEvalGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear n ℝ) := borel _
local instance realEvalGLBorel (n : ℕ) : BorelSpace (GeneralLinear n ℝ) := ⟨rfl⟩

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "G" => GeneralLinear n ℝ
local notation "Mat" => Matrix I I ℝ
local notation "Kc" => unitaryCompact ℝ n
local notation "ιg" => inverseTranspose n ℝ
local notation "dp" => ArchimedeanLocal.detPower realNormalizedAbs
local notation "D" => realMatrixDetScale (r := r)

theorem realMatrixDetScale_mul (x y : G) : D (x * y) = D x * D y := by
  simp only [realMatrixDetScale, realNormalizedAbs, Units.val_mul, Matrix.det_mul, abs_mul]

theorem realMatrixDetScale_inv (x : G) : D x⁻¹ = (D x)⁻¹ := by
  change |((Matrix.GeneralLinearGroup.det x⁻¹ : ℝˣ) : ℝ)| = |x.val.det|⁻¹
  rw [map_inv, Units.val_inv_eq_inv_val, Matrix.GeneralLinearGroup.val_det_apply, abs_inv]

theorem realDetPower_mul (x y : G) (s : ℂ) : dp (x * y) s = dp x s * dp y s := by
  simp only [realDetPower_eq_cpow]
  change (D (x * y) : ℂ) ^ s = (D x : ℂ) ^ s * (D y : ℂ) ^ s
  rw [realMatrixDetScale_mul, Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg (realMatrixDetScale_pos x).le (realMatrixDetScale_pos y).le]

theorem realDetPower_inv (x : G) (s : ℂ) : dp x⁻¹ s = (dp x s)⁻¹ := by
  simp only [realDetPower_eq_cpow]
  change (D x⁻¹ : ℂ) ^ s = ((D x : ℂ) ^ s)⁻¹
  rw [realMatrixDetScale_inv, Complex.ofReal_inv,
    Complex.inv_cpow_ofReal_nonneg (realMatrixDetScale_pos x).le]

private theorem realMatrixDetScale_inverseTranspose_inv (x : G) : D (ιg x)⁻¹ = D x := by
  rw [realMatrixDetScale_inv]
  change (realNormalizedAbs (ιg x).val.det)⁻¹ = realNormalizedAbs x.val.det
  rw [realNormalizedAbs_det_inverseTranspose, inv_inv]

private theorem shift_rank_power (x : G) : (dp x ((r : ℂ) / 2)) ^ 2 * (D x : ℂ) = (D x : ℂ) ^ n := by
  have hx : (D x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (realMatrixDetScale_pos x).ne'
  rw [realDetPower_eq_cpow]
  change ((D x : ℂ) ^ ((r : ℂ) / 2)) ^ 2 * (D x : ℂ) = _
  rw [pow_two, ← Complex.cpow_add _ _ hx, show (r : ℂ) / 2 + (r : ℂ) / 2 = r by ring,
    Complex.cpow_natCast, pow_succ]

private theorem translated_transform (Φ : 𝓢(Mat, ℂ)) (x g : G) :
    matrixTransform 1 (rectangularTranslate x⁻¹ 1 Φ) g.val =
      (D x : ℂ) ^ n * matrixTransform 1 Φ ((ιg x)⁻¹ * g).val := by
  rw [matrixTransform_translate, map_inv, map_one, Units.val_one, Matrix.det_one, abs_one,
    one_pow, mul_one, Matrix.mul_one, Units.val_mul]
  change (((D x⁻¹ ^ n)⁻¹ : ℝ) : ℂ) * _ = _
  rw [realMatrixDetScale_inv, inv_pow, inv_inv, Complex.ofReal_pow]

private theorem theta_left_primal (μ : Measure G) [μ.IsHaarMeasure]
    (f : G → ℂ) (Φ : 𝓢(Mat, ℂ)) (x : G) (h : ℝ → ℂ) (a : ℝ) :
    theta μ (realMatrixBaseKernel (fun g => f (x * g)) Φ) D h a =
      (dp x ((r : ℂ) / 2))⁻¹ * theta μ (realMatrixBaseKernel f (rectangularTranslate x⁻¹ 1 Φ))
        D h (a / D x) := by
  let P (g : G) := realMatrixBaseKernel (fun y => f (x * y)) Φ g * h (a * D g)
  change (∫ g, P g ∂μ) = _
  rw [← integral_mul_left_eq_self (μ := μ) P x⁻¹, theta, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all μ fun g => ?_)
  simp only [P, realMatrixBaseKernel, mul_inv_cancel_left, rectangularTranslate_apply, Units.val_one,
    Matrix.mul_one, Units.val_mul, realDetPower_mul, realDetPower_inv,
    realMatrixDetScale_mul, realMatrixDetScale_inv, div_eq_mul_inv, mul_assoc]
  ring

private theorem theta_left_dual (μ : Measure G) [μ.IsHaarMeasure]
    (f : G → ℂ) (Φ : 𝓢(Mat, ℂ)) (x : G) (k : ℝ → ℂ) (v : ℝ) :
    theta μ (realMatrixBaseKernel (fun g => f (x * ιg g)) (matrixTransform 1 Φ)) D k v =
      (dp x ((r : ℂ) / 2) * ((D x : ℂ) ^ n)⁻¹) *
        theta μ (realMatrixBaseKernel (f ∘ ιg) (matrixTransform 1 (rectangularTranslate x⁻¹ 1 Φ)))
          D k (v * D x) := by
  let Q (g : G) := realMatrixBaseKernel (fun y => f (x * ιg y)) (matrixTransform 1 Φ) g * k (v * D g)
  change (∫ g, Q g ∂μ) = _
  rw [← integral_mul_left_eq_self (μ := μ) Q (ιg x)⁻¹, theta, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all μ fun g => ?_)
  have hx : (D x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (realMatrixDetScale_pos x).ne'
  have hd : dp (ιg x)⁻¹ ((r : ℂ) / 2) = dp x ((r : ℂ) / 2) := by
    simp only [realDetPower_eq_cpow]
    change (D (ιg x)⁻¹ : ℂ) ^ ((r : ℂ) / 2) = (D x : ℂ) ^ ((r : ℂ) / 2)
    rw [realMatrixDetScale_inverseTranspose_inv]
  simp only [Q, realMatrixBaseKernel, realMatrixDetScale_mul,
    realMatrixDetScale_inverseTranspose_inv, realDetPower_mul, hd, map_mul, map_inv,
    inverseTranspose_involutive, mul_inv_cancel_left, Function.comp_apply, translated_transform]
  simp only [mul_assoc]
  rw [← mul_assoc (((D x : ℂ) ^ n)⁻¹), inv_mul_cancel₀ (pow_ne_zero _ hx), one_mul]
  ring

/-- If the standard-character theta identity holds at evaluation at the identity for all
Schwartz tests, it holds with the same reflection factor at every left evaluation point. -/
theorem realMatrix_theta_of_left_evaluation (μ : Measure G) [μ.IsHaarMeasure]
    (f : G → ℂ) (h k : ℝ → ℂ) (x : G)
    (hθ : ∀ (Ψ : 𝓢(Mat, ℂ)) (a : ℝ), 0 < a →
      theta μ (realMatrixBaseKernel f Ψ) D h a = (a : ℂ) *
        theta μ (realMatrixBaseKernel (f ∘ ιg) (matrixTransform 1 Ψ)) D k a⁻¹)
    (Φ : 𝓢(Mat, ℂ)) {a : ℝ} (ha : 0 < a) :
    theta μ (realMatrixBaseKernel (fun g => f (x * g)) Φ) D h a = (a : ℂ) *
      theta μ (realMatrixBaseKernel (fun g => f (x * ιg g)) (matrixTransform 1 Φ)) D k a⁻¹ := by
  have hD := realMatrixDetScale_pos x
  have hx : (D x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hD.ne'
  have hd : dp x ((r : ℂ) / 2) ≠ 0 := by
    rw [realDetPower_eq_cpow]
    exact Complex.cpow_ne_zero_iff.mpr (Or.inl hx)
  have hs : (a / D x)⁻¹ = a⁻¹ * D x := by
    rw [div_eq_mul_inv, mul_inv, inv_inv, mul_comm]
  have hc : (dp x ((r : ℂ) / 2))⁻¹ * ((a / D x : ℝ) : ℂ) =
      (a : ℂ) * (dp x ((r : ℂ) / 2) * ((D x : ℂ) ^ n)⁻¹) := by
    rw [Complex.ofReal_div, ← shift_rank_power, pow_two]
    field_simp
  rw [theta_left_primal, theta_left_dual,
    hθ _ _ (div_pos ha hD), hs, ← mul_assoc, hc, mul_assoc]

/-- The matrix theta identity at any left evaluation point of a position-principal-series
section, for any rapidly decreasing determinant-scale kernel pair satisfying the torus theta
identity at every scale for all Schwartz tests. -/
theorem realMatrix_position_theta_left_evaluation_of_pair (μ : Measure G) [μ.IsHaarMeasure]
    (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (χ : ℕ → ℝˣ → ℂ) (e : I → Fin 2) (u : I → ℂ)
    (hχ : ∀ (i : I) (x : ℝˣ), χ i x = charFun (e i) (u i) x)
    (f : G → ℂ) (hf : f ∈ principalSeries ℝ n χ) {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hb : ∀ g, ‖f g‖ ≤ C * realMatrixHeight g ^ N)
    (Hk Kk : ℝ → ℂ) (hHm : Measurable Hk) (hKm : Measurable Kk)
    (hHr : RapidDecay Hk) (hKr : RapidDecay Kk)
    (hpair : ∀ (Ψ : 𝓢(I → ℝ, ℂ)) (t : ℝ), 0 < t →
      theta volume (weightedKernel e u Ψ) detScale Hk t =
        (t : ℂ) * theta volume (weightedKernel e (-u) (ArchimedeanTateTheta.fourierInvN Ψ)) detScale Kk t⁻¹)
    (x : G) (Φ : 𝓢(Mat, ℂ)) {a : ℝ} (ha : 0 < a) :
    theta μ (realMatrixBaseKernel (fun g => f (x * g)) Φ) D (Hk) a = (a : ℂ) *
      theta μ (realMatrixBaseKernel (fun g => f (x * ιg g)) (matrixTransform 1 Φ)) D (Kk) a⁻¹ := by
  apply realMatrix_theta_of_left_evaluation μ f (Hk) (Kk) x _ Φ ha
  intro Ψ t ht
  have hfc : Continuous f := hf.1.continuous
  have hdc : Continuous (f ∘ ιg) := hfc.comp (continuous_inverseTranspose n ℝ)
  have hbd (g : G) : ‖(f ∘ ιg) g‖ ≤ C * realMatrixHeight g ^ N := by
    simpa only [Function.comp_apply, realMatrixHeight_inverseTranspose] using hb (ιg g)
  let T : ℝ := (n : ℝ) + 2 * N
  have hT : (n : ℝ) + 2 * N ≤ T + (r : ℝ) / 2 := le_add_of_nonneg_right (by positivity)
  exact realMatrix_theta_at_one_of_pair μ κ χ e u hχ f hf Ψ (a := t) Hk Kk hHm hKm
    (fun Ψ' => hpair Ψ' t ht)
    (integrable_realMatrix_theta_kernel μ hfc Ψ (Hk) (hHm) (hHr) ht
      (integrable_realMatrixBaseKernel_power μ hfc.measurable Ψ hC hb hT))
    (integrable_realMatrix_theta_kernel μ hdc (matrixTransform 1 Ψ) (Kk) (hKm)
      (hKr) (inv_pos.mpr ht)
      (integrable_realMatrixBaseKernel_power μ hdc.measurable (matrixTransform 1 Ψ) hC hbd hT))

/-- The real torus pair identity at any left evaluation point of a position-principal-series
section. Both the same point and the same section occur on the two sides. -/
theorem realMatrix_position_theta_left_evaluation (μ : Measure G) [μ.IsHaarMeasure]
    (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (χ : ℕ → ℝˣ → ℂ) (e : I → Fin 2) (u : I → ℂ)
    (hχ : ∀ (i : I) (x : ℝˣ), χ i x = charFun (e i) (u i) x)
    (f : G → ℂ) (hf : f ∈ principalSeries ℝ n χ) {C : ℝ} {N : ℕ} (hC : 0 ≤ C)
    (hb : ∀ g, ‖f g‖ ≤ C * realMatrixHeight g ^ N)
    (x : G) (Φ : 𝓢(Mat, ℂ)) {a : ℝ} (ha : 0 < a) :
    theta μ (realMatrixBaseKernel (fun g => f (x * g)) Φ) D (detH e u) a = (a : ℂ) *
      theta μ (realMatrixBaseKernel (fun g => f (x * ιg g)) (matrixTransform 1 Φ)) D (detK e u) a⁻¹ :=
  realMatrix_position_theta_left_evaluation_of_pair μ κ χ e u hχ f hf hC hb (detH e u) (detK e u)
    (measurable_detH e u) (measurable_detK e u) (rapidDecay_detH e u) (rapidDecay_detK e u)
    (fun Ψ _ ht => torus_theta_of_schwartz Ψ e u ht) x Φ ha

end Langlands.GodementJacquet
