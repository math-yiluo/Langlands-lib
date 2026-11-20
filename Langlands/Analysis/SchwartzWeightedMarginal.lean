import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Distribution.SchwartzSpace.Basic

/-! # Weighted marginals of Schwartz functions -/

noncomputable section

open Filter MeasureTheory
open scoped ContDiff Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private def sliceDerivative (Φ : SchwartzMap (E × F) ℂ) (n : ℕ) (x : E) (y : F) :=
  iteratedFDeriv ℝ n (fun v => Φ (v, y)) x

private theorem slice_smooth (Φ : SchwartzMap (E × F) ℂ) (y : F) :
    ContDiff ℝ ∞ (fun x => Φ (x, y)) :=
  Φ.smooth'.comp (contDiff_id.prodMk contDiff_const)

private theorem sliceDerivative_eq (Φ : SchwartzMap (E × F) ℂ) (n : ℕ) (x : E) (y : F) :
    sliceDerivative Φ n x y =
      (iteratedFDeriv ℝ n Φ (x, y)).compContinuousLinearMap
        (fun _ => ContinuousLinearMap.inl ℝ E F) := by
  let L := ContinuousLinearMap.inl ℝ E F
  let H : E × F → ℂ := fun p => Φ (p + (0, y))
  have hH : ContDiff ℝ ∞ H := Φ.smooth'.comp (contDiff_id.add contDiff_const)
  change iteratedFDeriv ℝ n (fun v => Φ (v, y)) x = _
  have hL : (fun v => Φ (v, y)) = H ∘ L := by
    funext v
    simp [H, L]
  rw [hL, L.iteratedFDeriv_comp_right hH x (by simp)]
  change (iteratedFDeriv ℝ n (fun p : E × F => Φ (p + (0, y))) (L x)).compContinuousLinearMap
    (fun _ => L) = _
  rw [iteratedFDeriv_comp_add_right]
  simp [L]

private theorem continuous_sliceDerivative (Φ : SchwartzMap (E × F) ℂ) (n : ℕ) :
    Continuous (fun p : E × F => sliceDerivative Φ n p.1 p.2) := by
  simp only [sliceDerivative_eq, Prod.mk.eta]
  let L := ContinuousMultilinearMap.compContinuousLinearMapL (F := ℂ)
    (fun _ : Fin n => ContinuousLinearMap.inl ℝ E F)
  exact L.continuous.comp ((Φ.smooth n).continuous_iteratedFDeriv le_rfl)

private theorem norm_sliceDerivative_le (Φ : SchwartzMap (E × F) ℂ) (n : ℕ) (x : E) (y : F) :
    ‖sliceDerivative Φ n x y‖ ≤ ‖iteratedFDeriv ℝ n Φ (x, y)‖ := by
  rw [sliceDerivative_eq]
  exact (iteratedFDeriv ℝ n Φ (x, y)).norm_compContinuous_linearIsometry_le
    (fun _ => LinearIsometry.inl ℝ E F)

private def sliceBound (Φ : SchwartzMap (E × F) ℂ) (q n : ℕ) : ℝ :=
  (2 : ℝ) ^ q * (Finset.Iic (q, n)).sup (schwartzSeminormFamily ℝ (E × F) ℂ) Φ

private theorem norm_weighted_sliceDerivative_le (Φ : SchwartzMap (E × F) ℂ)
    (κ : F → ℂ) (k q n : ℕ) (x : E) (y : F) :
    ‖x‖ ^ k * ‖κ y • sliceDerivative Φ n x y‖ ≤
      sliceBound Φ (k + q) n * (‖κ y‖ * ((1 + ‖y‖) ^ q)⁻¹) := by
  have h : ‖x‖ ^ k * (1 + ‖y‖) ^ q * ‖sliceDerivative Φ n x y‖ ≤
      sliceBound Φ (k + q) n := calc
    _ ≤ (1 + ‖(x, y)‖) ^ k * (1 + ‖(x, y)‖) ^ q *
        ‖iteratedFDeriv ℝ n Φ (x, y)‖ := by
      gcongr
      · exact (norm_fst_le (x, y)).trans (le_add_of_nonneg_left zero_le_one)
      · exact norm_snd_le (x, y)
      · exact norm_sliceDerivative_le Φ n x y
    _ ≤ _ := by
      rw [← pow_add]
      exact SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
        (m := (k + q, n)) le_rfl le_rfl Φ (x, y)
  rw [norm_smul, ← mul_assoc (sliceBound Φ _ _), ← div_eq_mul_inv,
    le_div_iff₀ (by positivity)]
  convert mul_le_mul_of_nonneg_right h (norm_nonneg (κ y)) using 1
  ring

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- Integration against a measurable weight with integrable polynomially damped
norm preserves Schwartz decay in the other variable. -/
def schwartzWeightedMarginal (μ : Measure F) (κ : F → ℂ) (hκ : Measurable κ) (q : ℕ)
    (hI : Integrable (fun y => ‖κ y‖ * ((1 + ‖y‖) ^ q)⁻¹) μ)
    (Φ : SchwartzMap (E × F) ℂ) : SchwartzMap E ℂ := by
  let D (n : ℕ) (x : E) (y : F) := κ y • sliceDerivative Φ n x y
  have hmeas (n : ℕ) (x : E) : AEStronglyMeasurable (D n x) μ :=
    hκ.aestronglyMeasurable.smul
      (((continuous_sliceDerivative Φ n).comp
        (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
  have hbound (n : ℕ) (x : E) (y : F) :
      ‖D n x y‖ ≤ sliceBound Φ q n * (‖κ y‖ * ((1 + ‖y‖) ^ q)⁻¹) := by
    simpa only [D, pow_zero, one_mul, zero_add] using
      norm_weighted_sliceDerivative_le Φ κ 0 q n x y
  have hintegrable (n : ℕ) (x : E) : Integrable (D n x) μ :=
    (hI.const_mul (sliceBound Φ q n)).mono' (hmeas n x)
      (Eventually.of_forall (hbound n x))
  let p : E → FormalMultilinearSeries ℝ E ℂ := fun x n => ∫ y, D n x y ∂μ
  have hd (n : ℕ) (x : E) :
      HasFDerivAt (fun v => p v n) (p x (n + 1)).curryLeft x := by
    let C := continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) ℂ
    let e := C.toContinuousLinearEquiv
    let L := e.toContinuousLinearMap
    have hdiff (v : E) (y : F) :
        HasFDerivAt (fun w => D n w y) (L (D (n + 1) v y)) v := by
      have h := (slice_smooth Φ y).ftaylorSeries.fderiv n
        (ENat.natCast_lt_of_coe_top_le_withTop le_rfl n) v
      exact h.const_smul (κ y)
    have h := hasFDerivAt_integral_of_dominated_of_fderiv_le
      (s := Set.univ) (univ_mem : Set.univ ∈ 𝓝 x)
      (Eventually.of_forall (hmeas n)) (hintegrable n x)
      (L.continuous.comp_aestronglyMeasurable (hmeas (n + 1) x))
      (Eventually.of_forall fun y v _ => by
        change ‖L (D (n + 1) v y)‖ ≤ _
        rw [show ‖L (D (n + 1) v y)‖ = ‖D (n + 1) v y‖ from C.norm_map _]
        exact hbound (n + 1) v y)
      (hI.const_mul (sliceBound Φ q (n + 1)))
      (Eventually.of_forall fun y v _ => hdiff v y)
    have hL : (∫ y, L (D (n + 1) x y) ∂μ) = L (∫ y, D (n + 1) x y ∂μ) := by
      change (∫ y, e (D (n + 1) x y) ∂μ) = e (∫ y, D (n + 1) x y ∂μ)
      exact ContinuousLinearEquiv.integral_comp_comm (μ := μ) (𝕜 := ℝ)
        (E := E [×(n + 1)]→L[ℝ] ℂ) (F := E →L[ℝ] E [×n]→L[ℝ] ℂ)
        e (D (n + 1) x)
    rw [hL] at h
    exact h
  let g : E → ℂ := fun x => ∫ y, κ y * Φ (x, y) ∂μ
  have hg : HasFTaylorSeriesUpTo ∞ g p := {
    zero_eq := fun x => by
      change (∫ y, D 0 x y ∂μ) (fun _ => 0) = _
      rw [ContinuousMultilinearMap.integral_apply (hintegrable 0 x)]
      simp only [D, g, sliceDerivative, smul_apply,
        iteratedFDeriv_zero_apply, smul_eq_mul]
    fderiv := fun n _ x => hd n x
    cont := fun n _ => continuous_iff_continuousAt.2 fun x => (hd n x).continuousAt }
  refine ⟨g, ⟨p, hg⟩, fun k n => ?_⟩
  let B (y : F) := ‖κ y‖ * ((1 + ‖y‖) ^ q)⁻¹
  refine ⟨sliceBound Φ (k + q) n * ∫ y, B y ∂μ, fun x => ?_⟩
  rw [← hg.eq_iteratedFDeriv (by simp : (n : ℕ∞ω) ≤ ∞)]
  change ‖x‖ ^ k * ‖∫ y, D n x y ∂μ‖ ≤ _
  calc
    _ ≤ ‖x‖ ^ k * ∫ y, ‖D n x y‖ ∂μ :=
      mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (by positivity)
    _ = ∫ y, ‖x‖ ^ k * ‖D n x y‖ ∂μ := (integral_const_mul _ _).symm
    _ ≤ ∫ y, sliceBound Φ (k + q) n * B y ∂μ :=
      integral_mono ((hintegrable n x).norm.const_mul _) (hI.const_mul _)
        (norm_weighted_sliceDerivative_le Φ κ k q n x)
    _ = _ := integral_const_mul _ _

@[simp]
theorem schwartzWeightedMarginal_apply (μ : Measure F) (κ : F → ℂ) (hκ : Measurable κ)
    (q : ℕ) (hI : Integrable (fun y => ‖κ y‖ * ((1 + ‖y‖) ^ q)⁻¹) μ)
    (Φ : SchwartzMap (E × F) ℂ) (x : E) :
    schwartzWeightedMarginal μ κ hκ q hI Φ x = ∫ y, κ y * Φ (x, y) ∂μ := rfl

/-- A bounded measurable weight preserves the Schwartz class under integration
in one variable against a measure of temperate growth. -/
def schwartzBoundedMarginal (μ : Measure F) [μ.HasTemperateGrowth] (κ : F → ℂ)
    (hκ : Measurable κ) {C : ℝ} (hC : ∀ y, ‖κ y‖ ≤ C)
    (Φ : SchwartzMap (E × F) ℂ) : SchwartzMap E ℂ :=
  schwartzWeightedMarginal μ κ hκ μ.integrablePower
    (by
      have he (y : F) : (1 + ‖y‖) ^ (-(μ.integrablePower : ℝ)) =
          ((1 + ‖y‖) ^ μ.integrablePower)⁻¹ := by
        rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
      have h : Integrable (fun y : F => ((1 + ‖y‖) ^ μ.integrablePower)⁻¹) μ := by
        simpa only [he] using μ.integrable_pow_neg_integrablePower
      refine (h.const_mul C).mono' (hκ.norm.mul
        (((continuous_const.add continuous_norm).pow _).measurable.inv)).aestronglyMeasurable
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (hC y) (by positivity)) Φ

@[simp]
theorem schwartzBoundedMarginal_apply (μ : Measure F) [μ.HasTemperateGrowth] (κ : F → ℂ)
    (hκ : Measurable κ) {C : ℝ} (hC : ∀ y, ‖κ y‖ ≤ C)
    (Φ : SchwartzMap (E × F) ℂ) (x : E) :
    schwartzBoundedMarginal μ κ hκ hC Φ x = ∫ y, κ y * Φ (x, y) ∂μ := rfl

omit [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
/-- Fixing the second coordinate of a Schwartz function gives a Schwartz
function of the first coordinate. -/
def schwartzSlice (Φ : SchwartzMap (E × F) ℂ) (y : F) : SchwartzMap E ℂ :=
  SchwartzMap.compCLMOfAntilipschitz ℂ
    ((ContinuousLinearMap.inl ℝ E F).hasTemperateGrowth.add
      (Function.HasTemperateGrowth.const (0, y)))
    (show AntilipschitzWith 1 (fun x : E => (x, 0) + (0, y)) from
      (show Isometry (fun x : E => (x, (0 : F)) + (0, y)) from
        (isometry_add_right (0, y)).comp (LinearIsometry.inl ℝ E F).isometry).antilipschitzWith) Φ

omit [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] in
@[simp]
theorem schwartzSlice_apply (Φ : SchwartzMap (E × F) ℂ) (y : F) (x : E) :
    schwartzSlice Φ y x = Φ (x, y) := by
  change Φ ((x, (0 : F)) + (0, y)) = _
  simp

end Langlands.Analysis
