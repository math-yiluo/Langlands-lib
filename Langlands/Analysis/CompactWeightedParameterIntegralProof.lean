import Langlands.Analysis.CompactWeightedParameterIntegralStatement
import Langlands.Analysis.CompactWeightedIntegral

noncomputable section

universe uX uV uH uE

namespace Langlands.Analysis

open MeasureTheory Set
open scoped ContDiff

/-- Smoothness follows by integrating a smooth supremum-norm scalar family. -/
theorem compactWeightedParameterIntegral :
    CompactWeightedParameterIntegralStatement.{uX, uV, uH, uE} := by
  intro X _ _ _ _ V _ _ H _ _ E _ _ _ μ _ w j s hs t ht hj h hh
  classical
  let f (p : V) : C(X, ℂ) :=
    if hp : p ∈ s then
      ⟨fun x => h (p, j x), hh.continuousOn.comp_continuous
        (continuous_const.prodMk j.continuous) (fun x => ⟨hp, hj x⟩)⟩
    else 0
  have heq : ∀ p ∈ s, ∀ x, f p x = h (p, j x) := by
    intro p hp x
    simp only [f, dite_eq_left hp, ContinuousMap.coe_mk]
  have hf : ContDiffOn ℝ ∞ f s :=
    contDiffOn_infty_compactFamily_of_joint j hs ht hj hh heq
  constructor
  · intro p hp
    simpa only [heq p hp] using compactWeightedIntegral_integrable μ w (f p)
  · have hI := (compactWeightedIntegral μ w).restrictScalars ℝ |>.contDiff.comp_contDiffOn hf
    apply hI.congr
    intro p hp
    change (∫ x, h (p, j x) • w x ∂μ) = (∫ x, f p x • w x ∂μ)
    exact integral_congr_ae (Filter.Eventually.of_forall fun x =>
      congrArg (fun z : ℂ => z • w x) (heq p hp x).symm)

end Langlands.Analysis
