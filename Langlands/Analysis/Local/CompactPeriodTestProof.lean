import Langlands.Analysis.Local.CompactPeriodTestStatement
import Mathlib.Topology.ContinuousMap.Bounded.Normed

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory Set
open scoped CompactlySupported Pointwise

universe uG uX

/-- The exact weighted compact-domain test construction. -/
theorem compactPeriodTest : CompactPeriodTestStatement.{uG, uX} := by
  intro G _ _ _ _ _ X _ _ _ μ _ s hs hsc j hj w hw f
  let F : G → ℂ := fun g => ∫ x in s, w x * f ((j x)⁻¹ * g) ∂μ
  obtain ⟨B, hB⟩ := hsc.exists_bound_of_continuousOn hw.continuousOn
  let Cw : ℝ := max B 0
  let Cf : ℝ := ‖f.toBoundedContinuousFunction‖
  have hwbound : ∀ x ∈ s, ‖w x‖ ≤ Cw := by
    intro x hx
    exact (hB x (subset_closure hx)).trans (le_max_left _ _)
  have hfbound : ∀ y, ‖f y‖ ≤ Cf := f.toBoundedContinuousFunction.norm_coe_le_norm
  have hμs : μ s < ⊤ := (measure_mono subset_closure).trans_lt hsc.measure_lt_top
  have hb : Integrable (fun _ : X => Cw * Cf) (μ.restrict s) :=
    integrableOn_const hμs.ne
  have hmeas : ∀ g : G,
      AEStronglyMeasurable (fun x => w x * f ((j x)⁻¹ * g)) (μ.restrict s) := by
    intro g
    exact (hw.mul (f.continuous.comp (hj.inv.mul_const g))).aestronglyMeasurable
  have hbound : ∀ g : G, ∀ᵐ x ∂μ.restrict s, ‖w x * f ((j x)⁻¹ * g)‖ ≤ Cw * Cf := by
    intro g
    filter_upwards [ae_restrict_mem hs] with x hx
    rw [norm_mul]
    exact mul_le_mul (hwbound x hx) (hfbound _) (norm_nonneg _)
      (le_max_right _ _)
  have hint : ∀ g, Integrable (fun x => w x * f ((j x)⁻¹ * g)) (μ.restrict s) :=
    fun g => hb.mono' (hmeas g) (hbound g)
  have hcont : Continuous F := by
    apply continuous_of_dominated hmeas hbound hb
    exact Filter.Eventually.of_forall fun x =>
      continuous_const.mul (f.continuous.comp (continuous_const.mul continuous_id))
  let K : Set G := (j '' closure s) * tsupport f
  have hK : IsCompact K := (hsc.image hj).mul f.hasCompactSupport
  have hsupport : Function.support F ⊆ K := by
    intro g hg
    by_contra hgK
    apply hg
    apply integral_eq_zero_of_ae
    filter_upwards [ae_restrict_mem hs] with x hx
    have hz : f ((j x)⁻¹ * g) = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro ht
      apply hgK
      exact ⟨j x, ⟨x, subset_closure hx, rfl⟩, (j x)⁻¹ * g, ht, by simp⟩
    simp only [hz, mul_zero, Pi.zero_apply]
  have hc : HasCompactSupport F :=
    hK.of_isClosed_subset (isClosed_tsupport F) (closure_minimal hsupport hK.isClosed)
  refine ⟨hint, ⟨⟨F, hcont⟩, hc⟩, ?_, ?_⟩
  · intro g
    rfl
  · exact closure_minimal hsupport hK.isClosed

end Langlands.QuotientIntegration
