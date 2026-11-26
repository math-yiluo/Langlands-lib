import Langlands.Global.RankinSelberg.RealMatrixEvaluationTransport
import Langlands.Global.RankinSelberg.RealMatrixCompactFunctional

/-! # The real matrix functional equation for compact-derivative-bounded coefficients -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear
open Langlands.LocalFactor.Archimedean (RealBlock)
open Langlands.Global.RankinSelbergGlobal
open ArchimedeanLocal ArchimedeanMellinPair ArchimedeanDeterminantTheta RealSquareFourier RealPrincipalSeries

local instance realFunctionGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear n ℝ) := borel _
local instance realFunctionGLBorel (n : ℕ) : BorelSpace (GeneralLinear n ℝ) := ⟨rfl⟩

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "G" => GeneralLinear n ℝ
local notation "Mat" => Matrix I I ℝ
local notation "Kc" => unitaryCompact ℝ n
local notation "ιg" => inverseTranspose n ℝ
local notation "D" => realMatrixDetScale (r := r)
local notation "H" => @realMatrixHeight n

private def matrixThetaWeight (Φ : Mat → ℂ) (h : ℝ → ℂ) (a : ℝ) (g : G) : ℂ :=
  realMatrixBaseKernel (fun _ => 1) Φ g * h (a * D g)

private theorem measurable_matrixThetaWeight {Φ : Mat → ℂ} (hΦ : Continuous Φ)
    {h : ℝ → ℂ} (hh : Measurable h) (a : ℝ) : Measurable (matrixThetaWeight Φ h a) :=
  (measurable_realMatrixBaseKernel continuous_const hΦ).mul
    (hh.comp (measurable_realMatrixDetScale.const_mul _))

private theorem theta_eq_integral_matrixThetaWeight (μ : Measure G) (f : G → ℂ)
    (Φ : Mat → ℂ) (h : ℝ → ℂ) (a : ℝ) :
    theta μ (realMatrixBaseKernel f Φ) D h a = ∫ g, matrixThetaWeight Φ h a g * f g ∂μ := by
  refine integral_congr_ae (ae_of_all μ fun g => ?_)
  simp only [realMatrixBaseKernel, matrixThetaWeight, mul_one]
  ring

private theorem integrable_norm_matrixThetaWeight_mul_height (μ : Measure G) [μ.IsHaarMeasure]
    (Φ : 𝓢(Mat, ℂ)) (h : ℝ → ℂ) (hh : Measurable h) (hd : RapidDecay h) {a : ℝ} (ha : 0 < a) (m : ℕ) :
    Integrable (fun g => ‖matrixThetaWeight Φ h a g‖ * H g ^ m) μ := by
  let f (g : G) : ℂ := (H g ^ m : ℝ)
  have hfc : Continuous f := Complex.continuous_ofReal.comp (continuous_realMatrixHeight.pow _)
  have hfn (g : G) : ‖f g‖ = H g ^ m := by
    simp only [f, Complex.norm_real, Real.norm_of_nonneg (pow_nonneg (RealPlaceRestriction.realMatrixHeight_nonneg g) m)]
  have hB (g : G) : ‖f g‖ ≤ 1 * H g ^ m := by rw [hfn, one_mul]
  let T : ℝ := (n : ℝ) + 2 * m
  have hT : (n : ℝ) + 2 * m ≤ T + (r : ℝ) / 2 := le_add_of_nonneg_right (by positivity)
  have hi := integrable_realMatrixBaseKernel_power μ hfc.measurable Φ zero_le_one hB hT
  refine (integrable_realMatrix_theta_kernel μ hfc Φ h hh hd ha hi).norm.congr (ae_of_all μ fun g => ?_)
  simp only [matrixThetaWeight, realMatrixBaseKernel, mul_one, norm_mul, hfn]
  ring

/-- Any rapidly decreasing determinant kernel pair satisfying the torus theta identity for the
position characters reflects the real matrix theta integral of any compact-derivative-bounded
principal-series coefficient at Fourier parameter one. -/
theorem realMatrix_functional_theta_at_one_of_pair (μ : Measure G) [μ.IsHaarMeasure]
    (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (ds : List RealBlock) (f : principalSeries ℝ n (realPositionCharacter ds))
    (ℓ : principalSeries ℝ n (realPositionCharacter ds) →ₗ[ℂ] ℂ)
    (hℓ : HasCompactDerivativeBound r ds ℓ)
    (Hk Kk : ℝ → ℂ) (hHm : Measurable Hk) (hKm : Measurable Kk)
    (hHr : RapidDecay Hk) (hKr : RapidDecay Kk)
    (hpair : ∀ (Ψ : 𝓢(I → ℝ, ℂ)) (t : ℝ), 0 < t →
      theta volume (weightedKernel (fun i : I => RealBlockPosition.realPositionSign ds i)
          (fun i : I => GramFormula.realPositionExponent ds i) Ψ) detScale Hk t =
        (t : ℂ) * theta volume (weightedKernel (fun i : I => RealBlockPosition.realPositionSign ds i)
          (-fun i : I => GramFormula.realPositionExponent ds i)
          (ArchimedeanTateTheta.fourierInvN Ψ)) detScale Kk t⁻¹)
    (Φ : 𝓢(Mat, ℂ)) {a : ℝ} (ha : 0 < a) :
    let F (g : G) := ℓ (translate r ds g f)
    theta μ (realMatrixBaseKernel F Φ) D (Hk) a =
      (a : ℂ) * theta μ (realMatrixBaseKernel (F ∘ ιg) (matrixTransform 1 Φ)) D (Kk) a⁻¹ := by
  intro F
  let e (i : I) := RealBlockPosition.realPositionSign ds i
  let u (i : I) := GramFormula.realPositionExponent ds i
  let W := matrixThetaWeight Φ (Hk) a
  let V := matrixThetaWeight (matrixTransform 1 Φ) (Kk) a⁻¹
  let W' (g : G) := (a : ℂ) * V g
  have hW : Measurable W := measurable_matrixThetaWeight Φ.continuous (hHm) a
  have hV : Measurable V := measurable_matrixThetaWeight (matrixTransform 1 Φ).continuous (hKm) a⁻¹
  have hW' : Measurable W' := hV.const_mul _
  have hI (m : ℕ) : Integrable (fun g => ‖W g‖ * H g ^ m) μ :=
    integrable_norm_matrixThetaWeight_mul_height μ Φ _ (hHm) (hHr) ha m
  have hI' (m : ℕ) : Integrable (fun g => ‖W' g‖ * H g ^ m) μ := by
    have hi : Integrable (fun g => ‖V g‖ * H g ^ m) μ :=
      integrable_norm_matrixThetaWeight_mul_height μ (matrixTransform 1 Φ) _ (hKm)
        (hKr) (inv_pos.mpr ha) m
    simpa only [W', norm_mul, mul_assoc] using hi.const_mul ‖(a : ℂ)‖
  obtain ⟨N, hN⟩ := exists_uniform_principalSeries_derivative_height r ds
  obtain ⟨C, hC, hB⟩ := hN f f.2 []
  have hE (x : G) : (∫ g, W g * (f : G → ℂ) (x * id g) ∂μ) =
      ∫ g, W' g * (f : G → ℂ) (x * ιg g) ∂μ := by
    have hθ := realMatrix_position_theta_left_evaluation_of_pair μ κ (realPositionCharacter ds) e u
      (fun i z => RealBlockPosition.realPositionCharacter_eq_charFun ds i z) f f.2 hC hB Hk Kk hHm hKm hHr hKr hpair x Φ ha
    rw [theta_eq_integral_matrixThetaWeight, theta_eq_integral_matrixThetaWeight] at hθ
    simpa only [W, W', V, id_eq, mul_assoc (a : ℂ), integral_const_mul] using hθ
  have hFun := integral_compactFunctional_eq_of_evaluation_eq μ hW.aestronglyMeasurable
    hW'.aestronglyMeasurable hI hI' continuous_id (continuous_inverseTranspose n ℝ)
    (fun _ => rfl) realMatrixHeight_inverseTranspose f ℓ hℓ hE
  rw [theta_eq_integral_matrixThetaWeight, theta_eq_integral_matrixThetaWeight]
  simpa only [W, W', V, F, Function.comp_apply, id_eq, mul_assoc (a : ℂ), integral_const_mul] using hFun

/-- The explicit convolved Tate pair reflects the real matrix theta integral of any
compact-derivative-bounded principal-series coefficient at Fourier parameter one. -/
theorem realMatrix_functional_theta_at_one (μ : Measure G) [μ.IsHaarMeasure]
    (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (ds : List RealBlock) (f : principalSeries ℝ n (realPositionCharacter ds))
    (ℓ : principalSeries ℝ n (realPositionCharacter ds) →ₗ[ℂ] ℂ)
    (hℓ : HasCompactDerivativeBound r ds ℓ) (Φ : 𝓢(Mat, ℂ)) {a : ℝ} (ha : 0 < a) :
    let e (i : I) := RealBlockPosition.realPositionSign ds i
    let u (i : I) := GramFormula.realPositionExponent ds i
    let F (g : G) := ℓ (translate r ds g f)
    theta μ (realMatrixBaseKernel F Φ) D (detH e u) a =
      (a : ℂ) * theta μ (realMatrixBaseKernel (F ∘ ιg) (matrixTransform 1 Φ)) D (detK e u) a⁻¹ :=
  realMatrix_functional_theta_at_one_of_pair μ κ ds f ℓ hℓ _ _ (measurable_detH _ _)
    (measurable_detK _ _) (rapidDecay_detH _ _) (rapidDecay_detK _ _)
    (fun Ψ _ ht => torus_theta_of_schwartz Ψ _ _ ht) Φ ha

/-- Real matrix continuation and reflection at the standard positive character for
coefficients of compact-derivative-bounded linear forms. -/
def RealMatrixCompactFunctionalEquationAtOneStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (ds : List RealBlock) (f : principalSeries ℝ n (realPositionCharacter ds))
    (ℓ : principalSeries ℝ n (realPositionCharacter ds) →ₗ[ℂ] ℂ),
    HasCompactDerivativeBound r ds ℓ → ∀ (Φ : 𝓢(Mat, ℂ)),
    let e (i : I) := RealBlockPosition.realPositionSign ds i
    let u (i : I) := GramFormula.realPositionExponent ds i
    let F (g : G) := ℓ (translate r ds g f)
    HasRealMatrixEquation μ F Φ (F ∘ ιg) (matrixTransform 1 Φ)
      (torusL e u) (torusL e (-u)) (fun _ => torusEpsilon e)

theorem realMatrixCompactFunctionalEquationAtOne : RealMatrixCompactFunctionalEquationAtOneStatement (r := r) := by
  intro μ hμ κ hκ hκs ds f ℓ hℓ Φ e u F
  have hFc : Continuous F := continuous_compactFunctionalCoefficient ℓ hℓ f
  have hFdc : Continuous (F ∘ ιg) := hFc.comp (continuous_inverseTranspose n ℝ)
  obtain ⟨N, hN⟩ := compactFunctionalGrowth r ds ℓ hℓ
  obtain ⟨C, hC, hB⟩ := hN f
  have hBd (g : G) : ‖(F ∘ ιg) g‖ ≤ C * H g ^ N := by
    simpa only [Function.comp_apply, realMatrixHeight_inverseTranspose] using hB (ιg g)
  exact realMatrix_continuation_of_theta μ e u hFc hFdc Φ (matrixTransform 1 Φ) hC hC hB hBd
    (fun a ha => realMatrix_functional_theta_at_one μ κ ds f ℓ hℓ Φ (a := a) ha)

end Langlands.GodementJacquet
