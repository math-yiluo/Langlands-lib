import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Schwartz averages along uniformly controlled linear maps -/

noncomputable section

open Filter MeasureTheory
open scoped ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis

variable {E F P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace P] [SecondCountableTopology P] [MeasurableSpace P] [OpensMeasurableSpace P]

omit [SecondCountableTopology P] [MeasurableSpace P] [OpensMeasurableSpace P] in
private theorem continuous_linearPullbackDerivative (Φ : SchwartzMap F ℂ) (n : ℕ) (x : E)
    {L : P → E →L[ℝ] F} (hL : Continuous L) :
    Continuous (fun y => iteratedFDeriv ℝ n (Φ ∘ L y) x) := by
  let C := ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ
    (fun _ : Fin n => E) (fun _ : Fin n => F) ℂ
  have hC : Continuous (fun y => C (fun _ : Fin n => L y)) :=
    C.coe_continuous.comp (continuous_pi fun _ => hL)
  have hΦ : Continuous (fun y => iteratedFDeriv ℝ n Φ (L y x)) :=
    ((Φ.smooth n).continuous_iteratedFDeriv le_rfl).comp (hL.clm_apply continuous_const)
  have h (y : P) :
      iteratedFDeriv ℝ n (Φ ∘ L y) x = C (fun _ => L y) (iteratedFDeriv ℝ n Φ (L y x)) :=
    (L y).iteratedFDeriv_comp_right (Φ.smooth' : ContDiff ℝ ∞ Φ) x (by simp)
  simp only [h]
  exact hC.clm_apply hΦ

omit [TopologicalSpace P] [SecondCountableTopology P] [MeasurableSpace P] [OpensMeasurableSpace P] in
/-- A pointwise weighted derivative bound for the pullback by a linear map. -/
theorem norm_pow_mul_linearPullbackDerivative_le (Φ : SchwartzMap F ℂ)
    (k n : ℕ) (x : E) (L : E →L[ℝ] F) {A B : ℝ} (hA : ‖L‖ ≤ A)
    (hB₀ : 0 ≤ B) (hB : ‖x‖ ≤ B * ‖L x‖) :
    ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (Φ ∘ L) x‖ ≤
      (B ^ k * A ^ n) * SchwartzMap.seminorm ℝ k n Φ := by
  have hΦ : ContDiff ℝ ∞ (Φ : F → ℂ) := Φ.smooth'
  rw [L.iteratedFDeriv_comp_right hΦ x (by simp)]
  have hnorm := (iteratedFDeriv ℝ n Φ (L x)).norm_compContinuousLinearMap_le (fun _ => L)
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hnorm
  have hAn : ‖L‖ ^ n ≤ A ^ n := pow_le_pow_left₀ (norm_nonneg _) hA _
  calc
    _ ≤ (B * ‖L x‖) ^ k * (‖iteratedFDeriv ℝ n Φ (L x)‖ * A ^ n) :=
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hB _) (hnorm.trans
        (mul_le_mul_of_nonneg_left hAn (norm_nonneg _))) (norm_nonneg _)
        (pow_nonneg ((norm_nonneg x).trans hB) _)
    _ = (B ^ k * A ^ n) * (‖L x‖ ^ k * ‖iteratedFDeriv ℝ n Φ (L x)‖) := by
      rw [mul_pow]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (SchwartzMap.le_seminorm ℝ k n Φ (L x))
      (mul_nonneg (pow_nonneg hB₀ _) (pow_nonneg ((norm_nonneg _).trans hA) _))

/-- Averaging pullbacks of a Schwartz function by a continuous family of
uniformly bounded and uniformly bounded-below linear maps gives a Schwartz
function. The averaging weight is integrable. -/
def schwartzLinearAverage (μ : Measure P) (κ : P → ℂ) (hκ : Integrable κ μ)
    (L : P → E →L[ℝ] F) (hL : Continuous L) {A B : ℝ}
    (hA : ∀ y, ‖L y‖ ≤ A) (hB₀ : 0 ≤ B) (hB : ∀ y x, ‖x‖ ≤ B * ‖L y x‖)
    (Φ : SchwartzMap F ℂ) : SchwartzMap E ℂ := by
  let D (n : ℕ) (x : E) (y : P) := κ y • iteratedFDeriv ℝ n (Φ ∘ L y) x
  let C (k n : ℕ) := (B ^ k * A ^ n) * SchwartzMap.seminorm ℝ k n Φ
  have hmeas (n : ℕ) (x : E) : AEStronglyMeasurable (D n x) μ :=
    hκ.aestronglyMeasurable.smul
      (continuous_linearPullbackDerivative Φ n x hL).aestronglyMeasurable
  have hbound (k n : ℕ) (x : E) (y : P) :
      ‖x‖ ^ k * ‖D n x y‖ ≤ C k n * ‖κ y‖ := by
    dsimp only [D]
    rw [norm_smul, ← mul_assoc, mul_comm (‖x‖ ^ k), mul_assoc, mul_comm (C k n)]
    exact mul_le_mul_of_nonneg_left
      (norm_pow_mul_linearPullbackDerivative_le Φ k n x (L y) (hA y) hB₀ (hB y x)) (norm_nonneg _)
  have hintegrable (n : ℕ) (x : E) : Integrable (D n x) μ :=
    (hκ.norm.const_mul (C 0 n)).mono' (hmeas n x)
      (Eventually.of_forall fun y => by simpa only [pow_zero, one_mul] using hbound 0 n x y)
  let p : E → FormalMultilinearSeries ℝ E ℂ := fun x n => ∫ y, D n x y ∂μ
  have hd (n : ℕ) (x : E) :
      HasFDerivAt (fun v => p v n) (p x (n + 1)).curryLeft x := by
    let curry := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℂ
    let e := curry.toContinuousLinearEquiv
    have hdiff (v : E) (y : P) :
        HasFDerivAt (fun z => D n z y) (e (D (n + 1) v y)) v := by
      have hΦ : ContDiff ℝ ∞ (Φ ∘ L y) := Φ.smooth'.comp_continuousLinearMap
      have h := hΦ.ftaylorSeries.fderiv n (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n) v
      exact h.const_smul (κ y)
    have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := Set.univ) (univ_mem : Set.univ ∈ 𝓝 x)
      (Eventually.of_forall (hmeas n)) (hintegrable n x)
      (e.continuous.comp_aestronglyMeasurable (hmeas (n + 1) x))
      (Eventually.of_forall fun y v _ => by
        change ‖e (D (n + 1) v y)‖ ≤ C 0 (n + 1) * ‖κ y‖
        rw [show ‖e (D (n + 1) v y)‖ = ‖D (n + 1) v y‖ from curry.norm_map _]
        simpa only [pow_zero, one_mul] using hbound 0 (n + 1) v y)
      (hκ.norm.const_mul (C 0 (n + 1)))
      (Eventually.of_forall fun y v _ => hdiff v y)
    rw [ContinuousLinearEquiv.integral_comp_comm (μ := μ) (𝕜 := ℝ)
      (E := E [×(n + 1)]→L[ℝ] ℂ) (F := E →L[ℝ] E [×n]→L[ℝ] ℂ)
      e (D (n + 1) x)] at h
    exact h
  let g (x : E) := ∫ y, κ y * Φ (L y x) ∂μ
  have hg : HasFTaylorSeriesUpTo ∞ g p := {
    zero_eq := fun x => by
      change (∫ y, D 0 x y ∂μ) (fun _ => 0) = _
      rw [ContinuousMultilinearMap.integral_apply (hintegrable 0 x)]
      simp only [D, g, smul_apply, iteratedFDeriv_zero_apply, Function.comp_apply, smul_eq_mul]
    fderiv := fun n _ x => hd n x
    cont := fun n _ => continuous_iff_continuousAt.2 fun x => (hd n x).continuousAt }
  refine ⟨g, ⟨p, hg⟩, fun k n => ?_⟩
  refine ⟨C k n * ∫ y, ‖κ y‖ ∂μ, fun x => ?_⟩
  rw [← hg.eq_iteratedFDeriv (by simp : (n : ℕ∞ω) ≤ ∞)]
  change ‖x‖ ^ k * ‖∫ y, D n x y ∂μ‖ ≤ _
  calc
    _ ≤ ‖x‖ ^ k * ∫ y, ‖D n x y‖ ∂μ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = ∫ y, ‖x‖ ^ k * ‖D n x y‖ ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ y, C k n * ‖κ y‖ ∂μ :=
      integral_mono ((hintegrable n x).norm.const_mul _) (hκ.norm.const_mul _)
        (hbound k n x)
    _ = _ := integral_const_mul _ _

@[simp]
theorem schwartzLinearAverage_apply (μ : Measure P) (κ : P → ℂ) (hκ : Integrable κ μ)
    (L : P → E →L[ℝ] F) (hL : Continuous L) {A B : ℝ}
    (hA : ∀ y, ‖L y‖ ≤ A) (hB₀ : 0 ≤ B) (hB : ∀ y x, ‖x‖ ≤ B * ‖L y x‖)
    (Φ : SchwartzMap F ℂ) (x : E) :
    schwartzLinearAverage μ κ hκ L hL hA hB₀ hB Φ x = ∫ y, κ y * Φ (L y x) ∂μ := rfl

end Langlands.Analysis
