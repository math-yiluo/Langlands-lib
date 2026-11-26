import Langlands.Global.RankinSelberg.RealAdjacentGodementHalfPlane
import Langlands.Global.RankinSelberg.RealMatrixTheta
import Langlands.Global.RankinSelberg.RealMatrixConvergence
import Langlands.Global.RankinSelberg.RealPrincipalSeriesHeight
import Langlands.Representation.Archimedean.RealBlockPositionData

/-! # Real matrix continuation from the determinant theta identity -/

noncomputable section

open MeasureTheory Filter Set
open scoped Matrix.Norms.Operator SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.GodementJacquet

open Langlands.Archimedean Langlands.GeneralLinear Langlands.GroupScheme.GeneralLinear
open Langlands.LocalFactor.Archimedean (RealBlock)
open Langlands.Archimedean.RealJacquetFrobenius (charFun)
open Langlands.Global.RankinSelbergGlobal
open ArchimedeanLocal ArchimedeanMellinPair ArchimedeanDeterminantTheta RealSquareFourier

local instance realContGLMeasurable (n : ℕ) : MeasurableSpace (GeneralLinear n ℝ) := borel _
local instance realContGLBorel (n : ℕ) : BorelSpace (GeneralLinear n ℝ) := ⟨rfl⟩
local instance realContMatrixSecondCountable (n : ℕ) :
    SecondCountableTopology (Matrix (Fin n) (Fin n) ℝ) :=
  inferInstanceAs (SecondCountableTopology (Fin n → Fin n → ℝ))
local instance realContGLSecondCountable (n : ℕ) : SecondCountableTopology (GeneralLinear n ℝ) :=
  Units.isOpenEmbedding_val.isInducing.secondCountableTopology

variable {r : ℕ}
local notation "n" => r + 1
local notation "I" => Fin n
local notation "G" => GeneralLinear n ℝ
local notation "Mat" => Matrix I I ℝ
local notation "Kc" => unitaryCompact ℝ n
local notation "ιg" => inverseTranspose n ℝ

/-- The standard real matrix zeta kernel, including the rank shift `r/2` for `n=r+1`. -/
def realMatrixZetaKernel (f : G → ℂ) (Φ : Mat → ℂ) (s : ℂ) (g : G) : ℂ :=
  Φ g.val * f g * ArchimedeanLocal.detPower realNormalizedAbs g (s + (r : ℂ) / 2)

/-- The normalized matrix zeta integral. -/
def realMatrixZeta (μ : Measure G) (f : G → ℂ) (Φ : Mat → ℂ) (s : ℂ) : ℂ :=
  ∫ g, realMatrixZetaKernel f Φ s g ∂μ

private theorem half_rank_re : ((r : ℂ) / 2).re = (r : ℝ) / 2 := by
  rw [show (r : ℂ) / 2 = (((r : ℝ) / 2 : ℝ) : ℂ) by push_cast; rfl, Complex.ofReal_re]

/-- The absolute real determinant power used by the initial zeta integral. -/
theorem realDetPower_eq_cpow {m : ℕ} (g : GeneralLinear m ℝ) (s : ℂ) :
    ArchimedeanLocal.detPower realNormalizedAbs g s = ((|g.val.det| : ℝ) : ℂ) ^ s := by
  have ha := abs_pos.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)
  rw [ArchimedeanLocal.detPower, realNormalizedAbs,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr ha.ne'), ← Complex.ofReal_log ha.le, mul_comm]

theorem realMatrixZetaKernel_eq (f : G → ℂ) (Φ : Mat → ℂ) (s : ℂ) (g : G) :
    realMatrixZetaKernel f Φ s g = realMatrixBaseKernel f Φ g * (realMatrixDetScale g : ℂ) ^ s := by
  have ha : 0 < |g.val.det| := realMatrixDetScale_pos g
  simp only [realMatrixZetaKernel, realMatrixBaseKernel, realMatrixDetScale, realNormalizedAbs,
    realDetPower_eq_cpow, Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne')]
  ring

/-- The matrix height is unchanged by inverse transpose. -/
theorem realMatrixHeight_inverseTranspose {m : ℕ} (g : GeneralLinear m ℝ) :
    realMatrixHeight (inverseTranspose m ℝ g) = realMatrixHeight g :=
  Langlands.Global.RankinSelbergGlobal.RealJacquet.realMatrixHeight_inverseTranspose g

/-- The absolute weighted norm of the base kernel is integrable for a large normalized
real parameter. -/
theorem integrable_realMatrixBaseKernel_power (μ : Measure G) [μ.IsHaarMeasure]
    {f : G → ℂ} (hf : Measurable f) (Φ : 𝓢(Mat, ℂ))
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (hb : ∀ g, ‖f g‖ ≤ C * realMatrixHeight g ^ N)
    {σ : ℝ} (hσ : (n : ℝ) + 2 * N ≤ σ + (r : ℝ) / 2) :
    Integrable (fun g => ‖realMatrixBaseKernel f Φ g‖ * realMatrixDetScale g ^ σ) μ := by
  refine (integrable_realMatrixWeightedNorm μ hf Φ hC hb hσ).congr (ae_of_all _ fun g => ?_)
  have hpos : 0 < |g.val.det| := realMatrixDetScale_pos g
  simp only [realMatrixBaseKernel, realMatrixDetScale, realNormalizedAbs, norm_mul, norm_realDetPower,
    half_rank_re, mul_assoc, ← Real.rpow_add hpos, add_comm σ]

/-- The rapid determinant kernels give absolutely convergent theta integrals from just
one integrable real weight. -/
theorem integrable_realMatrix_theta_kernel (μ : Measure G)
    {f : G → ℂ} (hf : Continuous f) (Φ : 𝓢(Mat, ℂ))
    (h : ℝ → ℂ) (hh : Measurable h) (hd : RapidDecay h) {a : ℝ} (ha : 0 < a) {σ : ℝ}
    (hσ : Integrable (fun g => ‖realMatrixBaseKernel f Φ g‖ * realMatrixDetScale g ^ σ) μ) :
    Integrable (fun g => realMatrixBaseKernel f Φ g * h (a * realMatrixDetScale g)) μ := by
  obtain ⟨B, hB⟩ := hd σ
  have hm : Measurable (fun g => realMatrixBaseKernel f Φ g * h (a * realMatrixDetScale g)) :=
    (measurable_realMatrixBaseKernel hf Φ.continuous).mul (hh.comp (measurable_realMatrixDetScale.const_mul _))
  refine (hσ.const_mul (B * a ^ σ)).mono' hm.aestronglyMeasurable (ae_of_all _ fun g => ?_)
  rw [norm_mul]
  have hp := realMatrixDetScale_pos g
  have h := hB (a * realMatrixDetScale g) (mul_pos ha hp)
  rw [Real.mul_rpow ha.le hp.le] at h
  calc
    _ ≤ ‖realMatrixBaseKernel f Φ g‖ * (B * (a ^ σ * realMatrixDetScale g ^ σ)) :=
      mul_le_mul_of_nonneg_left h (norm_nonneg _)
    _ = _ := by ring

/-- Convergence, holomorphy, continuation and a codiscrete functional equation for
two normalized real matrix integrals and specified scalar factors. -/
def HasRealMatrixEquation (μ : Measure G) (f : G → ℂ) (Φ : Mat → ℂ)
    (fd : G → ℂ) (Φd : Mat → ℂ) (L Ld E : ℂ → ℂ) : Prop :=
  ∃ (σ : ℝ) (M Md : ℂ → ℂ),
    (∀ s : ℂ, σ < s.re → Integrable (realMatrixZetaKernel f Φ s) μ ∧
      Integrable (realMatrixZetaKernel fd Φd s) μ) ∧
    DifferentiableOn ℂ (realMatrixZeta μ f Φ) {s : ℂ | σ < s.re} ∧
    DifferentiableOn ℂ (realMatrixZeta μ fd Φd) {s : ℂ | σ < s.re} ∧
    MeromorphicOn M univ ∧ MeromorphicOn Md univ ∧
    (∀ s : ℂ, σ < s.re → realMatrixZeta μ f Φ s = M s) ∧
    (∀ s : ℂ, σ < s.re → realMatrixZeta μ fd Φd s = Md s) ∧
    ∀ᶠ s in codiscrete ℂ, L s * Md (1 - s) = E s * Ld (1 - s) * M s

/-- The standard-character determinant theta identity supplies analytic continuation and the
functional equation for any two polynomially bounded continuous coefficients. -/
theorem realMatrix_continuation_of_theta (μ : Measure G) [μ.IsHaarMeasure]
    (e : I → Fin 2) (u : I → ℂ) {f fd : G → ℂ} (hf : Continuous f) (hfd : Continuous fd)
    (Φ Φd : 𝓢(Mat, ℂ)) {C Cd : ℝ} {N Nd : ℕ} (hC : 0 ≤ C) (hCd : 0 ≤ Cd)
    (hb : ∀ g, ‖f g‖ ≤ C * realMatrixHeight g ^ N) (hbd : ∀ g, ‖fd g‖ ≤ Cd * realMatrixHeight g ^ Nd)
    (hθ : ∀ a : ℝ, 0 < a → theta μ (realMatrixBaseKernel f Φ) realMatrixDetScale (detH e u) a =
      (a : ℂ) * theta μ (realMatrixBaseKernel fd Φd) realMatrixDetScale (detK e u) a⁻¹) :
    HasRealMatrixEquation μ f Φ fd Φd (torusL e u) (torusL e (-u)) (fun _ => torusEpsilon e) := by
  let T : ℝ := (n : ℝ) + 2 * max N Nd - (r : ℝ) / 2
  have ht (t : ℝ) (ht : T ≤ t) : (n : ℝ) + 2 * N ≤ t + (r : ℝ) / 2 := by
    have hN : (N : ℝ) ≤ ((max N Nd : ℕ) : ℝ) := by exact_mod_cast le_max_left N Nd
    dsimp [T] at ht
    linarith
  have htd (t : ℝ) (ht : T ≤ t) : (n : ℝ) + 2 * Nd ≤ t + (r : ℝ) / 2 := by
    have hNd : (Nd : ℝ) ≤ ((max N Nd : ℕ) : ℝ) := by exact_mod_cast le_max_right N Nd
    dsimp [T] at ht
    linarith
  obtain ⟨σ, M, Md, hM, hMd, hZ, hZd, hFE⟩ := determinant_pair_continuation e u μ μ
    (measurable_realMatrixBaseKernel hf Φ.continuous).aestronglyMeasurable
    (measurable_realMatrixBaseKernel hfd Φd.continuous).aestronglyMeasurable
    measurable_realMatrixDetScale measurable_realMatrixDetScale realMatrixDetScale_pos realMatrixDetScale_pos T
    (fun t ht' => integrable_realMatrixBaseKernel_power μ hf.measurable Φ hC hb (ht t ht'))
    (fun t ht' => integrable_realMatrixBaseKernel_power μ hfd.measurable Φd hCd hbd (htd t ht')) hθ
  refine ⟨max T σ, M, Md, ?_, ?_, ?_, hM, hMd, ?_, ?_, hFE⟩
  · intro s hs
    have hTs := ((le_max_left T σ).trans hs.le)
    exact ⟨integrable_realMatrixZetaKernel μ hf.measurable Φ hC hb
      (by simpa only [Complex.add_re, half_rank_re] using ht s.re hTs),
      integrable_realMatrixZetaKernel μ hfd.measurable Φd hCd hbd
        (by simpa only [Complex.add_re, half_rank_re] using htd s.re hTs)⟩
  · have hj := differentiableOn_realMatrixZetaIntegral μ hf.measurable Φ hC hb
    refine hj.comp (differentiable_id.add_const ((r : ℂ) / 2)).differentiableOn (fun s hs => ?_)
    have hTs : T < s.re := lt_of_le_of_lt (le_max_left T σ) hs
    have hst : T ≤ (T + s.re) / 2 := by linarith
    have hh := ht ((T + s.re) / 2) hst
    change (n : ℝ) + 2 * N < (s + (r : ℂ) / 2).re
    rw [Complex.add_re, half_rank_re]
    linarith
  · have hj := differentiableOn_realMatrixZetaIntegral μ hfd.measurable Φd hCd hbd
    refine hj.comp (differentiable_id.add_const ((r : ℂ) / 2)).differentiableOn (fun s hs => ?_)
    have hTs : T < s.re := lt_of_le_of_lt (le_max_left T σ) hs
    have hst : T ≤ (T + s.re) / 2 := by linarith
    have hh := htd ((T + s.re) / 2) hst
    change (n : ℝ) + 2 * Nd < (s + (r : ℂ) / 2).re
    rw [Complex.add_re, half_rank_re]
    linarith
  · intro s hs
    simp only [realMatrixZeta, realMatrixZetaKernel_eq]
    exact hZ s (lt_of_le_of_lt (le_max_right T σ) hs)
  · intro s hs
    simp only [realMatrixZeta, realMatrixZetaKernel_eq]
    exact hZd s (lt_of_le_of_lt (le_max_right T σ) hs)

/-- Standard-character equation for evaluation of a principal-series section at the group point. -/
theorem realMatrix_evaluation_equation_at_one (μ : Measure G) [μ.IsHaarMeasure]
    (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (χ : ℕ → ℝˣ → ℂ) (e : I → Fin 2) (u : I → ℂ)
    (hχ : ∀ (i : I) (x : ℝˣ), χ i x = charFun (e i) (u i) x)
    (f : G → ℂ) (hf : f ∈ principalSeries ℝ n χ) (Φ : 𝓢(Mat, ℂ))
    {C : ℝ} {N : ℕ} (hC : 0 ≤ C) (hb : ∀ g, ‖f g‖ ≤ C * realMatrixHeight g ^ N) :
    HasRealMatrixEquation μ f Φ (f ∘ ιg) (matrixTransform 1 Φ)
      (torusL e u) (torusL e (-u)) (fun _ => torusEpsilon e) := by
  have hfc : Continuous f := hf.1.continuous
  have hdc : Continuous (f ∘ ιg) := hfc.comp (continuous_inverseTranspose n ℝ)
  have hbd (g : G) : ‖(f ∘ ιg) g‖ ≤ C * realMatrixHeight g ^ N := by
    simpa only [Function.comp_apply, realMatrixHeight_inverseTranspose] using hb (ιg g)
  let T : ℝ := (n : ℝ) + 2 * N
  have ht : (n : ℝ) + 2 * N ≤ T + (r : ℝ) / 2 := le_add_of_nonneg_right (by positivity)
  have hi := integrable_realMatrixBaseKernel_power μ hfc.measurable Φ hC hb ht
  have hid := integrable_realMatrixBaseKernel_power μ hdc.measurable (matrixTransform 1 Φ) hC hbd ht
  exact realMatrix_continuation_of_theta μ e u hfc hdc Φ (matrixTransform 1 Φ) hC hC hb hbd
    (fun a ha => realMatrix_theta_at_one μ κ χ e u hχ f hf Φ ha
      (integrable_realMatrix_theta_kernel μ hfc Φ (detH e u) (measurable_detH e u) (rapidDecay_detH e u) ha hi)
      (integrable_realMatrix_theta_kernel μ hdc (matrixTransform 1 Φ) (detK e u) (measurable_detK e u)
        (rapidDecay_detK e u) (inv_pos.mpr ha) hid))

/-- The evaluation equation for the position characters of an actual inducing list. -/
def RealMatrixPositionEvaluationStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsHaarMeasure] (κ : Measure Kc) [κ.IsHaarMeasure] [SFinite κ]
    (ds : List RealBlock) (f : G → ℂ),
    f ∈ principalSeries ℝ n (realPositionCharacter ds) → ∀ (Φ : 𝓢(Mat, ℂ)),
    let e (i : I) := RealBlockPosition.realPositionSign ds i
    let u (i : I) := GramFormula.realPositionExponent ds i
    HasRealMatrixEquation μ f Φ (f ∘ ιg) (matrixTransform 1 Φ)
      (torusL e u) (torusL e (-u)) (fun _ => torusEpsilon e)

theorem realMatrixPositionEvaluation : RealMatrixPositionEvaluationStatement (r := r) := by
  intro μ hμ κ hκ hκs ds f hf Φ e u
  obtain ⟨N, hN⟩ := RealPrincipalSeries.exists_uniform_principalSeries_derivative_height r ds
  obtain ⟨C, hC, hb⟩ := hN f hf []
  exact realMatrix_evaluation_equation_at_one μ κ (realPositionCharacter ds) e u
    (fun i x => RealBlockPosition.realPositionCharacter_eq_charFun ds i x) f hf Φ hC hb

end Langlands.GodementJacquet
