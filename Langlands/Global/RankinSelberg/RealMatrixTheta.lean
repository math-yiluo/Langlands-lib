import Langlands.Global.RankinSelberg.RealTriangularMatched
import Langlands.Global.RankinSelberg.RealTriangularAdditiveDiagonal
import Langlands.Global.RankinSelberg.ArchimedeanDeterminantTheta

/-! # The real square matrix theta identity at the standard positive character -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal Matrix.Norms.Operator SchwartzMap Real

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear
open Langlands.Archimedean.RealJacquetFrobenius (charFun)
open Langlands.Global.RankinSelbergGlobal
open ArchimedeanLocal ArchimedeanMellinPair ArchimedeanTateTheta ArchimedeanDeterminantTheta
open Langlands.Global.RankinSelbergGlobal.RealSquareFourier
open Langlands.HarmonicAnalysis Langlands.LocalFactor.Archimedean

local instance realThetaGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear n ℝ) := borel _
local instance realThetaGLBorel (n : ℕ) : BorelSpace (GeneralLinear n ℝ) := ⟨rfl⟩
local instance realThetaUnitsMeasurable : MeasurableSpace ℝˣ := borel _
local instance realThetaUnitsBorel : BorelSpace ℝˣ := ⟨rfl⟩
local instance realThetaDiagonalSigmaFinite (n : ℕ) : SigmaFinite (realDiagonalHaar n) := by
  unfold realDiagonalHaar
  infer_instance

/-- The standard positive-sign Fourier integral on the diagonal in either notation. -/
theorem realFourierTransform_one_eq_fourierInvN {n : ℕ} (F : (Fin n → ℝ) → ℂ) :
    realFourierTransform 1 F = fourierInvN F := by
  have hμ : (realSelfDualMeasure (1 : ℝˣ)).measure = (volume : Measure ℝ) := by
    simp [realSelfDualMeasure]
  funext y
  rw [realFourierTransform, ArchimedeanLocal.fourierTransform, hμ, ← volume_pi, fourierInvN]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [UnitaryAdditiveCharacter.complex_apply, realScaledCharacter_apply, Units.val_one,
    one_mul, Real.fourierChar_apply, Complex.ofReal_mul, Complex.ofReal_ofNat, mul_comm (F x)]
  congr 2
  ring

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "Mat" => Matrix I I ℝ
local notation "G" => GeneralLinear n ℝ
local notation "Kc" => unitaryCompact ℝ n
local notation "D" => I → ℝˣ
local notation "ιg" => inverseTranspose n ℝ

/-- The normalized matrix kernel with the determinant-variable part left out. -/
def realMatrixBaseKernel (f : G → ℂ) (Φ : Mat → ℂ) (g : G) : ℂ :=
  Φ g.val * f g * detPower realNormalizedAbs g ((r : ℂ) / 2)

/-- The positive determinant scale on the group. -/
def realMatrixDetScale (g : G) : ℝ := realNormalizedAbs g.val.det

theorem realMatrixDetScale_pos (g : G) : 0 < realMatrixDetScale g :=
  abs_pos.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)

theorem measurable_realMatrixDetScale : Measurable (realMatrixDetScale (r := r)) :=
  (continuous_abs.comp Units.continuous_val.matrix_det).measurable

theorem measurable_realMatrixBaseKernel {f : G → ℂ} (hf : Continuous f)
    {Φ : Mat → ℂ} (hΦ : Continuous Φ) : Measurable (realMatrixBaseKernel f Φ) := by
  have hm := measurable_realMatrixWeightedIntegrand hf hΦ (h := fun _ => 1) measurable_const
  change Measurable (fun g : G => realMatrixBaseKernel f Φ g * 1) at hm
  simpa only [mul_one] using hm

private theorem realDiagonalAbs_eq_detScale (d : D) :
    realDiagonalAbs d = detScale (fun i => (d i : ℝ)) := by
  unfold realDiagonalAbs detScale
  exact Finset.prod_congr rfl fun i _ => (ite_eq_right (d i).ne_zero).symm

/-- A slice of the triangular diagonal integral is the additive torus theta integral,
with the compact value as a common scalar. -/
theorem integral_realDiagonalWeighted_eq_theta (χ : ℕ → ℝˣ → ℂ) (v : ℂ) (F : (I → ℝ) → ℂ)
    (hF : Measurable F) (h : ℝ → ℂ) (hh : Measurable h) (a : ℝ)
    (e : I → Fin 2) (u : I → ℂ) (hχ : ∀ (i : I) (x : ℝˣ), χ i x = charFun (e i) (u i) x) :
    (∫ d, realDiagonalWeightedIntegrand χ v F (fun t => h (a * t)) d ∂realDiagonalHaar n) =
      v * theta volume (weightedKernel e u F) detScale h a := by
  let T (x : I → ℝ) := F x * h (a * detScale x)
  have hT : Measurable T := hF.mul (hh.comp (measurable_detScale.const_mul _))
  have hL : ∀ d : D, realDiagonalWeightedIntegrand χ v F (fun t => h (a * t)) d =
      v * (T (fun i => (d i : ℝ)) * ∏ i, charFun (e i) (u i) (d i : ℝ)) := by
    intro d
    simp only [realDiagonalWeightedIntegrand, realDiagonalZetaWeight_eq, zero_mul,
      Complex.exp_zero, mul_one, realDiagonalAbs_eq_detScale d, T, hχ]
    ring
  simp_rw [hL, integral_const_mul]
  change v * (∫ d, T (fun i => (d i : ℝ)) * ∏ i, charFun (e i) (u i) (d i : ℝ)
    ∂Measure.pi (fun _ : I => RealRankZero.unitsHaar)) = _
  rw [(realDiagonalTateIntegration n e u T hT).2, theta]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  unfold weightedKernel T
  ring

/-- The torus theta identity for the convolved Tate pair and any Schwartz test. -/
theorem torus_theta_of_schwartz (Φ : 𝓢(I → ℝ, ℂ)) (e : I → Fin 2) (u : I → ℂ)
    {a : ℝ} (ha : 0 < a) :
    theta volume (weightedKernel e u Φ) detScale (detH e u) a =
      (a : ℂ) * theta volume (weightedKernel e (-u) (fourierInvN Φ)) detScale (detK e u) a⁻¹ := by
  let N : ℝ := 1 + ∑ i, |(u i).re|
  have hN (i : I) : |(u i).re| + 1 ≤ N := by
    dsimp [N]
    linarith [Finset.single_le_sum (fun j (_ : j ∈ Finset.univ) => abs_nonneg (u j).re)
      (Finset.mem_univ i)]
  refine determinant_theta_identity e u Φ.integrable (M := N) (Md := N) ?_ ?_ ha
  · exact integrable_weightedKernel_schwartz e u Φ N fun i => by
      linarith [hN i, neg_abs_le (u i).re]
  · rw [← funext (schwartzFourierInvN_apply Φ)]
    exact integrable_weightedKernel_schwartz e (-u) (schwartzFourierInvN Φ) N fun i => by
      simp only [Pi.neg_apply, Complex.neg_re]
      linarith [hN i, le_abs_self (u i).re]

/-- The matrix theta identity at evaluation at the identity for any determinant-scale kernel
pair `(Hk, Kk)` satisfying the torus theta identity for all Schwartz tests, once the two
weighted group integrands are integrable. -/
theorem realMatrix_theta_at_one_of_pair (μ : Measure G) [μ.IsHaarMeasure]
    (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (χ : ℕ → ℝˣ → ℂ) (e : I → Fin 2) (u : I → ℂ)
    (hχ : ∀ (i : I) (x : ℝˣ), χ i x = charFun (e i) (u i) x)
    (f : G → ℂ) (hf : f ∈ principalSeries ℝ n χ) (Φ : 𝓢(Mat, ℂ)) {a : ℝ}
    (Hk Kk : ℝ → ℂ) (hHm : Measurable Hk) (hKm : Measurable Kk)
    (hpair : ∀ Ψ : 𝓢(I → ℝ, ℂ), theta volume (weightedKernel e u Ψ) detScale Hk a =
      (a : ℂ) * theta volume (weightedKernel e (-u) (fourierInvN Ψ)) detScale Kk a⁻¹)
    (hP : Integrable (fun g => realMatrixBaseKernel f Φ g * Hk (a * realMatrixDetScale g)) μ)
    (hQ : Integrable (fun g => realMatrixBaseKernel (f ∘ ιg) (matrixTransform 1 Φ) g *
      Kk (a⁻¹ * realMatrixDetScale g)) μ) :
    theta μ (realMatrixBaseKernel f Φ) realMatrixDetScale (Hk) a =
      (a : ℂ) * theta μ (realMatrixBaseKernel (f ∘ ιg) (matrixTransform 1 Φ)) realMatrixDetScale
        (Kk) a⁻¹ := by
  let δ := realDiagonalHaar n
  let H (t : ℝ) := Hk (a * t)
  let T (t : ℝ) := Kk (a⁻¹ * t)
  have hH : Measurable H := (hHm).comp (measurable_const_mul _)
  have hT : Measurable T := (hKm).comp (measurable_const_mul _)
  let χd (i : ℕ) (x : ℝˣ) := χ i x⁻¹
  have hχd (i : I) (x : ℝˣ) : χd i x = charFun (e i) ((-u) i) x := by
    change χ i x⁻¹ = _
    rw [hχ i x⁻¹, Units.val_inv_eq_inv_val, realCharFun_inv _ _ x.ne_zero, Pi.neg_apply]
  let F (k : Kc) := realTriangularMarginal 1 Φ k
  let V (k : Kc) := realFourierTransform 1 (F k)
  have hV (k : Kc) : V k = fourierInvN (F k) := realFourierTransform_one_eq_fourierInvN _
  obtain ⟨c, _, h⟩ := realTriangularMatched (r := r) μ κ 1
  obtain ⟨hA, hP'⟩ := (h χ f hf Φ H hH).1 hP
  obtain ⟨hB, hQ'⟩ := (h χ f hf Φ T hT).2 hQ
  let A (p : Kc × D) := realDiagonalWeightedIntegrand χ (f p.1.val) (F p.1) H p.2
  let B (p : Kc × D) := realDiagonalWeightedIntegrand χd (f p.1.val) (V p.1) T p.2
  have hAe (k : Kc) : (∫ d, A (k, d) ∂δ) =
      f k.val * theta volume (weightedKernel e u (F k)) detScale (Hk) a :=
    integral_realDiagonalWeighted_eq_theta (r := r) χ (f k.val) (F k : (I → ℝ) → ℂ)
      (F k).continuous.measurable (Hk) (hHm) a e u hχ
  have hBe (k : Kc) : (∫ d, B (k, d) ∂δ) =
      f k.val * theta volume (weightedKernel e (-u) (fourierInvN (F k))) detScale (Kk) a⁻¹ := by
    have hm : Measurable (V k) := by
      rw [hV k]
      exact (continuous_fourierInvN (F k).integrable).measurable
    calc
      _ = f k.val * theta volume (weightedKernel e (-u) (V k)) detScale (Kk) a⁻¹ :=
        integral_realDiagonalWeighted_eq_theta (r := r) χd (f k.val) (V k) hm
          (Kk) (hKm) a⁻¹ e (-u) hχd
      _ = _ := by rw [hV k]
  change (∫ g, realMatrixWeightedIntegrand f Φ H g ∂μ) =
    (a : ℂ) * ∫ g, realMatrixWeightedIntegrand (f ∘ ιg) (matrixTransform 1 Φ) T g ∂μ
  rw [hP', hQ']
  change (c : ℂ) * (∫ p, A p ∂κ.prod δ) = (a : ℂ) * ((c : ℂ) * (∫ p, B p ∂κ.prod δ))
  rw [integral_prod A hA, integral_prod B hB, mul_left_comm (a : ℂ),
    ← integral_const_mul (μ := κ) (a : ℂ) (fun k : Kc => ∫ d, B (k, d) ∂δ)]
  apply congrArg (fun z : ℂ => (c : ℂ) * z)
  refine integral_congr_ae (ae_of_all κ fun k => ?_)
  change (∫ d, A (k, d) ∂δ) = (a : ℂ) * ∫ d, B (k, d) ∂δ
  rw [hAe k, hBe k, hpair (F k)]
  ring

/-- The standard-character matrix theta identity at evaluation at the identity, once the two
weighted group integrands are integrable. The determinant kernels are the convolved Tate pair. -/
theorem realMatrix_theta_at_one (μ : Measure G) [μ.IsHaarMeasure]
    (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (χ : ℕ → ℝˣ → ℂ) (e : I → Fin 2) (u : I → ℂ)
    (hχ : ∀ (i : I) (x : ℝˣ), χ i x = charFun (e i) (u i) x)
    (f : G → ℂ) (hf : f ∈ principalSeries ℝ n χ) (Φ : 𝓢(Mat, ℂ)) {a : ℝ} (ha : 0 < a)
    (hP : Integrable (fun g => realMatrixBaseKernel f Φ g * detH e u (a * realMatrixDetScale g)) μ)
    (hQ : Integrable (fun g => realMatrixBaseKernel (f ∘ ιg) (matrixTransform 1 Φ) g *
      detK e u (a⁻¹ * realMatrixDetScale g)) μ) :
    theta μ (realMatrixBaseKernel f Φ) realMatrixDetScale (detH e u) a =
      (a : ℂ) * theta μ (realMatrixBaseKernel (f ∘ ιg) (matrixTransform 1 Φ)) realMatrixDetScale
        (detK e u) a⁻¹ :=
  realMatrix_theta_at_one_of_pair μ κ χ e u hχ f hf Φ (detH e u) (detK e u)
    (measurable_detH e u) (measurable_detK e u) (fun Ψ => torus_theta_of_schwartz Ψ e u ha) hP hQ

end Langlands.GodementJacquet
