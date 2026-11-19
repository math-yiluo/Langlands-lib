import Langlands.Representation.Unitary.IntegratedTranslationPointwiseStatement
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

noncomputable section

universe uX uG

namespace Langlands.Analysis

open MeasureTheory
open scoped ENNReal

/-- The integrated translation action has the pointwise weighted integral as
an almost-everywhere representative. -/
theorem integratedTranslationPointwise :
    IntegratedTranslationPointwiseStatement.{uX, uG} := by
  intro X _ μX _ G _ _ μ _ act hact hpres π hπnorm hπmeas hcompat f hf φ
  -- A strongly measurable version of the weight.
  set f' : G → ℂ := hf.aestronglyMeasurable.mk f with hf'def
  have hf'sm : StronglyMeasurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk
  have hff' : f =ᵐ[μ] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hf'int : Integrable f' μ := hf.congr hff'
  have hφsm : StronglyMeasurable (φ : X → ℂ) := Lp.stronglyMeasurable φ
  have hactx : ∀ x, Measurable (fun g => act x g) := fun x =>
    hact.comp (measurable_const.prodMk measurable_id)
  have hactg : ∀ g, Measurable (fun x => act x g) := fun g =>
    hact.comp (measurable_id.prodMk measurable_const)
  -- The product integrand.
  set Φ : X × G → ℂ := fun p => f' p.2 * φ (act p.1 p.2) with hΦdef
  have hΦsm : StronglyMeasurable Φ :=
    (hf'sm.comp_measurable measurable_snd).mul (hφsm.comp_measurable hact)
  have hΦen : Measurable (fun p : X × G => ‖Φ p‖ₑ) := hΦsm.measurable.enorm
  -- An `L¹` bound on finite-measure sets, uniform in the group variable.
  have key : ∀ (B : Set X), MeasurableSet B → μX B < ∞ → ∀ g : G,
      ∫⁻ x in B, ‖φ (act x g)‖ₑ ∂μX ≤ μX B ^ (1 / 2 : ℝ) * eLpNorm φ 2 μX := by
    intro B hB hBfin g
    have hmeas : AEStronglyMeasurable (fun x => φ (act x g)) (μX.restrict B) :=
      (hφsm.comp_measurable (hactg g)).aestronglyMeasurable
    have hexp : (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) = (1 / 2 : ℝ) := by
      norm_num
    have hpres2 : eLpNorm (fun x => φ (act x g)) 2 μX = eLpNorm φ 2 μX :=
      eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable φ) (hpres g)
    rw [← eLpNorm_one_eq_lintegral_enorm hmeas]
    calc eLpNorm (fun x => φ (act x g)) 1 (μX.restrict B)
        ≤ eLpNorm (fun x => φ (act x g)) 2 (μX.restrict B) *
            (μX.restrict B) Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (2 : ℝ≥0∞).toReal) :=
          eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hmeas
      _ = eLpNorm (fun x => φ (act x g)) 2 (μX.restrict B) * μX B ^ (1 / 2 : ℝ) := by
          rw [Measure.restrict_apply_univ, hexp]
      _ ≤ eLpNorm (fun x => φ (act x g)) 2 μX * μX B ^ (1 / 2 : ℝ) := by
          gcongr
          exact Measure.restrict_le_self
      _ = μX B ^ (1 / 2 : ℝ) * eLpNorm φ 2 μX := by
          rw [mul_comm, hpres2]
  have hfin : ∀ (B : Set X), MeasurableSet B → μX B < ∞ →
      μX B ^ (1 / 2 : ℝ) * eLpNorm φ 2 μX * ∫⁻ g, ‖f' g‖ₑ ∂μ < ∞ := by
    intro B _ hBfin
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ?_ (Lp.eLpNorm_lt_top φ)) hf'int.2
    exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hBfin.ne
  -- Tonelli bound for the absolute product integrand.
  have dbl : ∀ (B : Set X), MeasurableSet B → μX B < ∞ →
      ∫⁻ x in B, ∫⁻ g, ‖Φ (x, g)‖ₑ ∂μ ∂μX ≤
        μX B ^ (1 / 2 : ℝ) * eLpNorm φ 2 μX * ∫⁻ g, ‖f' g‖ₑ ∂μ := by
    intro B hB hBfin
    rw [lintegral_lintegral_swap (f := fun x g => ‖Φ (x, g)‖ₑ) hΦen.aemeasurable]
    calc ∫⁻ g, ∫⁻ x in B, ‖Φ (x, g)‖ₑ ∂μX ∂μ
        = ∫⁻ g, ‖f' g‖ₑ * ∫⁻ x in B, ‖φ (act x g)‖ₑ ∂μX ∂μ := by
          congr 1
          funext g
          simp only [hΦdef, enorm_mul]
          rw [lintegral_const_mul' _ _ enorm_ne_top]
      _ ≤ ∫⁻ g, ‖f' g‖ₑ * (μX B ^ (1 / 2 : ℝ) * eLpNorm φ 2 μX) ∂μ := by
          gcongr with g
          exact key B hB hBfin g
      _ = μX B ^ (1 / 2 : ℝ) * eLpNorm φ 2 μX * ∫⁻ g, ‖f' g‖ₑ ∂μ := by
          rw [lintegral_mul_const _ hf'sm.measurable.enorm, mul_comm]
  -- Integrability of the product integrand on each finite-measure slab.
  have hΦint : ∀ (B : Set X), MeasurableSet B → μX B < ∞ →
      Integrable Φ ((μX.restrict B).prod μ) := by
    intro B hB hBfin
    refine ⟨hΦsm.aestronglyMeasurable, ?_⟩
    change ∫⁻ p, ‖Φ p‖ₑ ∂((μX.restrict B).prod μ) < ∞
    rw [lintegral_prod _ hΦen.aemeasurable]
    exact (dbl B hB hBfin).trans_lt (hfin B hB hBfin)
  -- Part (a): almost-everywhere absolute convergence.
  have hfinite_ae : ∀ᵐ x ∂μX, ∫⁻ g, ‖Φ (x, g)‖ₑ ∂μ < ∞ := by
    refine ae_of_forall_measure_lt_top_ae_restrict _ (fun B hB hBfin => ?_)
    exact ae_lt_top hΦen.lintegral_prod_right'
      ((dbl B hB hBfin).trans_lt (hfin B hB hBfin)).ne
  refine ⟨?_, ?_⟩
  · filter_upwards [hfinite_ae] with x hx
    have h' : Integrable (fun g => f' g * φ (act x g)) μ :=
      ⟨(hf'sm.mul (hφsm.comp_measurable (hactx x))).aestronglyMeasurable, hx⟩
    refine h'.congr ?_
    filter_upwards [hff'] with g hg
    simp only [hg]
  -- Part (b): identification by set integrals on finite-measure sets.
  have hFF' : (fun x => ∫ g, f g * φ (act x g) ∂μ) = fun x => ∫ g, Φ (x, g) ∂μ := by
    funext x
    apply integral_congr_ae
    filter_upwards [hff'] with g hg
    simp only [hΦdef, hg]
  have hR : integratedIsometricAction μ π hπnorm hπmeas f hf φ =
      ∫ g, f' g • π g φ ∂μ := by
    rw [integratedIsometricAction_apply]
    apply integral_congr_ae
    filter_upwards [hff'] with g hg
    rw [hg]
  rw [hFF', hR]
  have hvint : Integrable (fun g => f' g • π g φ) μ :=
    isometricActionIntegrand_integrable μ π hπnorm hπmeas f' hf'int φ
  refine ae_eq_of_forall_setIntegral_eq_of_sigmaFinite ?_ ?_ ?_
  · intro s _ hμs
    exact integrableOn_Lp_of_measure_ne_top _ (by norm_num) hμs.ne
  · intro s hs hμs
    refine ⟨hΦsm.integral_prod_right'.aestronglyMeasurable, ?_⟩
    change ∫⁻ x in s, ‖∫ g, Φ (x, g) ∂μ‖ₑ ∂μX < ∞
    calc ∫⁻ x in s, ‖∫ g, Φ (x, g) ∂μ‖ₑ ∂μX
        ≤ ∫⁻ x in s, ∫⁻ g, ‖Φ (x, g)‖ₑ ∂μ ∂μX :=
          lintegral_mono (fun x => enorm_integral_le_lintegral_enorm _)
      _ < ∞ := (dbl s hs hμs).trans_lt (hfin s hs hμs)
  · intro s hs hμs
    have hslice : ∀ g : G, ∫ x in s, (π g φ : X → ℂ) x ∂μX = ∫ x in s, φ (act x g) ∂μX :=
      fun g => integral_congr_ae (ae_restrict_of_ae (hcompat g φ))
    calc ∫ x in s, (∫ g, f' g • π g φ ∂μ : Lp ℂ 2 μX) x ∂μX
        = inner ℂ (indicatorConstLp 2 hs hμs.ne (1 : ℂ)) (∫ g, f' g • π g φ ∂μ) :=
          (L2.inner_indicatorConstLp_one hs hμs.ne _).symm
      _ = ∫ g, inner ℂ (indicatorConstLp 2 hs hμs.ne (1 : ℂ)) (f' g • π g φ) ∂μ :=
          (integral_inner hvint _).symm
      _ = ∫ g, f' g * ∫ x in s, φ (act x g) ∂μX ∂μ := by
          congr 1
          funext g
          rw [inner_smul_right, L2.inner_indicatorConstLp_one hs hμs.ne, hslice]
      _ = ∫ g, ∫ x in s, Φ (x, g) ∂μX ∂μ := by
          congr 1
          funext g
          simp only [hΦdef]
          rw [integral_const_mul]
      _ = ∫ x in s, ∫ g, Φ (x, g) ∂μ ∂μX :=
          (integral_integral_swap (f := fun x g => Φ (x, g)) (hΦint s hs hμs)).symm

end Langlands.Analysis
