import Langlands.Analysis.CountableCellLpStatement

/-! # Proof of the countable-cell Lp tests -/

namespace Langlands

open MeasureTheory
open scoped ENNReal NNReal

theorem countableCellLpUpper.{uX, uI} : CountableCellLpUpperStatement.{uX, uI} := by
  intro X _ I _ μ f p hp0 hpTop hf s hs b hb hsum
  apply (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpTop hf).2
  have hcell (i : I) :
      ∫⁻ x in s i, ‖f x‖ₑ ^ p.toReal ∂μ ≤ (b i) ^ p.toReal * μ (s i) := by
    calc
      _ ≤ ∫⁻ _ in s i, (b i) ^ p.toReal ∂μ :=
        setLIntegral_mono measurable_const
          (fun x hx => ENNReal.rpow_le_rpow (hb i x hx) ENNReal.toReal_nonneg)
      _ = _ := setLIntegral_const _ _
  have hcover :
      ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ ≤
        ∑' i, ∫⁻ x in s i, ‖f x‖ₑ ^ p.toReal ∂μ := by
    simpa only [hs, Measure.restrict_univ] using
      (lintegral_iUnion_le (μ := μ) s (fun x => ‖f x‖ₑ ^ p.toReal))
  exact lt_of_le_of_lt (hcover.trans (ENNReal.tsum_le_tsum hcell)) hsum

theorem countableCellLpLower.{uX, uI} : CountableCellLpLowerStatement.{uX, uI} := by
  intro X _ I _ μ f p hp0 hpTop hf s hs hd b hb
  have hcell (i : I) :
      (b i) ^ p.toReal * μ (s i) ≤ ∫⁻ x in s i, ‖f x‖ₑ ^ p.toReal ∂μ := by
    calc
      _ = ∫⁻ _ in s i, (b i) ^ p.toReal ∂μ := (setLIntegral_const _ _).symm
      _ ≤ _ := setLIntegral_mono' (hs i)
        (fun x hx => ENNReal.rpow_le_rpow (hb i x hx) ENNReal.toReal_nonneg)
  have hbound :
      (∑' i, (b i) ^ p.toReal * μ (s i)) ≤ ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ := by
    calc
      _ ≤ ∑' i, ∫⁻ x in s i, ‖f x‖ₑ ^ p.toReal ∂μ := ENNReal.tsum_le_tsum hcell
      _ = ∫⁻ x in ⋃ i, s i, ‖f x‖ₑ ^ p.toReal ∂μ :=
        (lintegral_iUnion hs hd _).symm
      _ ≤ _ := setLIntegral_le_lintegral _ _
  exact lt_of_le_of_lt hbound
    (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hpTop hf.eLpNorm_lt_top)

theorem countableCellLp.{uX, uI} : CountableCellLpStatement.{uX, uI} :=
  ⟨countableCellLpUpper, countableCellLpLower⟩

end Langlands
