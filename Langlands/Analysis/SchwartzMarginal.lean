import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Marginals of Schwartz functions on real vector spaces -/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal FourierTransform RealInnerProductSpace SchwartzMap

set_option autoImplicit false

namespace Langlands.Analysis.SchwartzMarginal

section InnerProduct

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

local notation "P" => WithLp 2 (E × F)

private def prodEquiv : P ≃L[ℝ] (E × F) := WithLp.prodContinuousLinearEquiv 2 ℝ E F

private def firstInclusion : E →L[ℝ] P :=
  (prodEquiv (E := E) (F := F)).symm.toContinuousLinearMap.comp (ContinuousLinearMap.inl ℝ E F)

private theorem isometry_firstInclusion : Isometry (firstInclusion (E := E) (F := F)) := by
  apply Isometry.of_dist_eq
  intro x y
  rw [dist_eq_norm, dist_eq_norm, ← map_sub]
  change ‖WithLp.toLp 2 (x - y, (0 : F))‖ = ‖x - y‖
  exact WithLp.norm_toLp_fst 2 E F _

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]

private def volumeMarginalCLM : 𝓢(E × F, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  (FourierTransform.fourierInvCLM ℂ 𝓢(E, ℂ)).comp
    ((SchwartzMap.compCLMOfAntilipschitz ℂ
      (firstInclusion (E := E) (F := F)).hasTemperateGrowth isometry_firstInclusion.antilipschitzWith).comp
        ((FourierTransform.fourierCLM ℂ 𝓢(P, ℂ)).comp
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (prodEquiv (E := E) (F := F)))))

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
private theorem continuous_integral_snd (Φ : 𝓢(E × F, ℂ)) :
    Continuous (fun x : E => ∫ y : F, Φ (x, y)) := by
  let k := Module.finrank ℝ F + 1
  let C : ℝ := 2 ^ k * ((Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2)) Φ
  let B : F → ℝ := fun y => max C 0 * (1 + ‖y‖) ^ (- (k : ℝ))
  have hk : (Module.finrank ℝ F : ℝ) < k := by
    exact_mod_cast Nat.lt_succ_self (Module.finrank ℝ F)
  have hB : Integrable B := (integrable_one_add_norm hk).const_mul _
  refine continuous_of_dominated (fun x => (Φ.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable)
    (fun x => ae_of_all _ fun y => ?_) hB (ae_of_all _ fun y =>
      Φ.continuous.comp (continuous_id.prodMk continuous_const))
  have hΦ := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) le_rfl le_rfl Φ (x, y)
  rw [norm_iteratedFDeriv_zero] at hΦ
  change ‖Φ (x, y)‖ ≤ B y
  dsimp only [B]
  rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv]
  apply (le_div_iff₀ (by positivity)).2
  calc
    _ ≤ ‖Φ (x, y)‖ * (1 + ‖(x, y)‖) ^ k := by
      apply mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ?_ _) (norm_nonneg _)
      gcongr
      exact norm_snd_le (x, y)
    _ ≤ C := by rw [mul_comm]; exact hΦ
    _ ≤ max C 0 := le_max_left _ _

private theorem fourier_integral_snd (Φ : 𝓢(E × F, ℂ)) (x : E) :
    𝓕 (fun u : E => ∫ v : F, Φ (u, v)) x =
      (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (prodEquiv (E := E) (F := F)) Φ))
        (firstInclusion (E := E) (F := F) x) := by
  let e := prodEquiv (E := E) (F := F)
  let j := firstInclusion (E := E) (F := F)
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ e Φ
  let K : P → ℂ := fun z => Real.fourierChar (-inner ℝ z (j x)) • g z
  have hK (p : E × F) : K (e.symm p) = Real.fourierChar (-inner ℝ p.1 x) • Φ p := by
    simp [K, g, j, e, firstInclusion, prodEquiv, WithLp.prod_inner_apply]
  have hΦ : Integrable (Φ : E × F → ℂ) ((volume : Measure E).prod (volume : Measure F)) :=
    Φ.integrable
  have hI : Integrable (fun p : E × F => Real.fourierChar (-inner ℝ p.1 x) • Φ p)
      ((volume : Measure E).prod (volume : Measure F)) := by
    refine hΦ.norm.mono' ?_ (ae_of_all _ fun p => ?_)
    · exact ((Real.continuous_fourierChar.comp ((continuous_fst.inner continuous_const).neg)).smul
        Φ.continuous).aestronglyMeasurable
    · rw [Circle.smul_def, norm_smul, Circle.norm_coe, one_mul]
  calc
    _ = ∫ p : E × F, Real.fourierChar (-inner ℝ p.1 x) • Φ p := by
      rw [Real.fourier_eq, Measure.volume_eq_prod E F, integral_prod _ hI]
      apply integral_congr_ae
      filter_upwards with u
      rw [Circle.smul_def, ← integral_smul]
      simp only [Circle.smul_def]
    _ = ∫ p : E × F, K (e.symm p) := by simp only [hK]
    _ = ∫ z, K z := (WithLp.volume_preserving_toLp E F).integral_comp'
      (f := MeasurableEquiv.toLp 2 (E × F)) K
    _ = _ := by rw [SchwartzMap.fourier_coe, Real.fourier_eq]

private theorem volumeMarginalCLM_apply (Φ : 𝓢(E × F, ℂ)) (x : E) :
    volumeMarginalCLM Φ x = ∫ y : F, Φ (x, y) := by
  let f : E → ℂ := fun u => ∫ v : F, Φ (u, v)
  let g := SchwartzMap.compCLMOfAntilipschitz ℂ (firstInclusion (E := E) (F := F)).hasTemperateGrowth
    isometry_firstInclusion.antilipschitzWith
    (𝓕 (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (prodEquiv (E := E) (F := F)) Φ))
  have hg : 𝓕 f = (g : E → ℂ) := funext fun u => fourier_integral_snd Φ u
  have hf : Integrable f := Φ.integrable.integral_prod_left
  have hi : Integrable (𝓕 f) := hg ▸ g.integrable
  have he := (continuous_integral_snd Φ).fourierInv_fourier_eq hf hi
  change (𝓕⁻ g) x = f x
  rw [SchwartzMap.fourierInv_coe, ← hg, he]

end InnerProduct

section FiniteDimensional

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

private def coordinates (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
  ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm

private def measureScale (μ : Measure F) [μ.IsAddHaarMeasure] : ℝ≥0 :=
  Measure.addHaarScalarFactor (μ.map (coordinates F)) volume

/-- The continuous complex-linear map given by integration along the second coordinate.
For an additive Haar measure its evaluation formula is `marginalCLM_apply`. -/
def marginalCLM (μ : Measure F) [μ.IsAddHaarMeasure] : 𝓢(E × F, ℂ) →L[ℂ] 𝓢(E, ℂ) :=
  ((measureScale μ : ℝ) : ℂ) •
    ((SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (coordinates E)).comp
      (volumeMarginalCLM.comp
        (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ ((coordinates E).prodCongr (coordinates F)).symm)))

@[simp]
theorem marginalCLM_apply (μ : Measure F) [μ.IsAddHaarMeasure] (Φ : 𝓢(E × F, ℂ)) (x : E) :
    marginalCLM μ Φ x = ∫ y : F, Φ (x, y) ∂μ := by
  let e := coordinates E
  let f := coordinates F
  let g := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (e.prodCongr f).symm Φ
  let c := measureScale μ
  have : (μ.map f).IsAddHaarMeasure := f.isAddHaarMeasure_map μ
  have hμ : μ.map f = c • volume := by
    exact Measure.isAddLeftInvariant_eq_smul (μ.map f) volume
  change (c : ℂ) • volumeMarginalCLM g (e x) = _
  rw [volumeMarginalCLM_apply]
  have hg (z : EuclideanSpace ℝ (Fin (Module.finrank ℝ F))) : g (e x, z) = Φ (x, f.symm z) := by
    simp [g]
  calc
    _ = (c : ℂ) • ∫ z, Φ (x, f.symm z) := by simp only [hg]
    _ = ∫ z, Φ (x, f.symm z) ∂μ.map f := by
      rw [hμ]
      change (c : ℂ) • _ = ∫ z, Φ (x, f.symm z) ∂(c : ℝ≥0∞) • volume
      rw [integral_smul_measure, ENNReal.coe_toReal, Complex.real_smul, smul_eq_mul]
    _ = ∫ y, Φ (x, f.symm (f y)) ∂μ :=
      integral_map_equiv f.toHomeomorph.toMeasurableEquiv (fun z => Φ (x, f.symm z))
    _ = _ := by
      simp only [ContinuousLinearEquiv.symm_apply_apply]

end FiniteDimensional

end Langlands.Analysis.SchwartzMarginal
