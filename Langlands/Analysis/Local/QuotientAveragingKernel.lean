import Langlands.Analysis.Local.QuotientPositiveLifting
import Langlands.Analysis.Local.QuotientTopology
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Integral

/-!
# Zero fiber averages have zero ambient Haar integral
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure
open scoped CompactlySupported Pointwise

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G) (hH : IsClosed (H : Set G))

include hH in
private theorem kernel_compact (f a : C_c(G, ℝ)) :
    HasCompactSupport (fun p : H × G => f (p.1.val * p.2) * a p.2) := by
  have hK : IsCompact ((Subtype.val : H → G) ⁻¹' (tsupport f * (tsupport a)⁻¹)) :=
    hH.isClosedEmbedding_subtypeVal.isCompact_preimage
      (f.hasCompactSupport.mul a.hasCompactSupport.inv)
  apply HasCompactSupport.of_support_subset_isCompact (hK.prod a.hasCompactSupport)
  intro p hp
  have hp' : f (p.1.val * p.2) ≠ 0 ∧ a p.2 ≠ 0 := mul_ne_zero_iff.mp hp
  have hf := subset_tsupport f hp'.1
  have ha := subset_tsupport a hp'.2
  refine ⟨?_, ha⟩
  change p.1.val ∈ tsupport f * (tsupport a)⁻¹
  exact ⟨p.1.val * p.2, hf, p.2⁻¹, by simpa using ha, by simp⟩

include hH in
private theorem kernel_inverse_compact (f a : C_c(G, ℝ)) :
    HasCompactSupport (fun p : H × G => f p.2 * a (p.1.val⁻¹ * p.2)) := by
  have hc := (kernel_compact H hH a f).comp_isClosedEmbedding
    ((Homeomorph.inv H).isClosedEmbedding.prodMap
      (Homeomorph.refl G).isClosedEmbedding)
  change HasCompactSupport (fun p : H × G => a (p.1.val⁻¹ * p.2) * f p.2) at hc
  simpa only [mul_comm] using hc

include hH in
private theorem kernel_fubini [MeasurableSpace G] [BorelSpace G]
    [MeasurableSpace H] [BorelSpace H]
    (μG : Measure G) (μH : Measure H)
    [IsFiniteMeasureOnCompacts μG] [IsMulLeftInvariant μG]
    [IsFiniteMeasureOnCompacts μH] (f a : C_c(G, ℝ)) :
    (∫ g, f g * (∫ h : H, a (h.val⁻¹ * g) ∂μH) ∂μG) =
      ∫ g, (∫ h : H, f (h.val * g) ∂μH) * a g ∂μG := by
  have hc₁ : Continuous (fun p : H × G => f p.2 * a (p.1.val⁻¹ * p.2)) :=
    (f.continuous.comp continuous_snd).mul
      (a.continuous.comp ((continuous_subtype_val.comp continuous_fst).inv.mul continuous_snd))
  have hc₂ : Continuous (fun p : H × G => f (p.1.val * p.2) * a p.2) :=
    (f.continuous.comp ((continuous_subtype_val.comp continuous_fst).mul continuous_snd)).mul
      (a.continuous.comp continuous_snd)
  have hs₁ : HasCompactSupport (fun p : H × G => f p.2 * a (p.1.val⁻¹ * p.2)) :=
    kernel_inverse_compact (G := G) H hH f a
  have hs₂ : HasCompactSupport (fun p : H × G => f (p.1.val * p.2) * a p.2) :=
    kernel_compact (G := G) H hH f a
  calc
    _ = ∫ g, ∫ h : H, f g * a (h.val⁻¹ * g) ∂μH ∂μG := by
      simp only [integral_const_mul]
    _ = ∫ h : H, ∫ g, f g * a (h.val⁻¹ * g) ∂μG ∂μH := by
      symm
      apply integral_integral_swap_of_hasCompactSupport
      · exact hc₁
      · exact hs₁
    _ = ∫ h : H, ∫ g, f (h.val * g) * a g ∂μG ∂μH := by
      apply integral_congr_ae
      filter_upwards [] with h
      simpa only [inv_mul_cancel_left] using
        (integral_mul_left_eq_self (μ := μG)
          (fun g => f g * a (h.val⁻¹ * g)) h.val).symm
    _ = ∫ g, ∫ h : H, f (h.val * g) * a g ∂μH ∂μG := by
      apply integral_integral_swap_of_hasCompactSupport
      · exact hc₂
      · exact hs₂
    _ = _ := by simp only [integral_mul_const]

private theorem kernel_zero_of_normalization
    (hnorm : RealQuotientCompactNormalization.{u}) :
    RealAveragingKernelIntegralZero.{u} := by
  intro G _ _ _ _ _ _ _ H hH _ _ μG μH _ _ _ _ _ _ f hf
  let : IsHaarMeasure μH.inv := ⟨⟩
  obtain ⟨a, _, ha⟩ := hnorm H hH μH.inv
    ((leftQuotientMap H) '' tsupport f)
    (f.hasCompactSupport.image (leftQuotient_isOpenQuotientMap H).continuous)
  have ha' (g : G) (hg : g ∈ tsupport f) :
      (∫ h : H, a (h.val⁻¹ * g) ∂μH) = 1 := by
    have hi := (MeasurableEquiv.inv H).measurableEmbedding.integral_map
      (μ := μH) (fun h : H => a (h.val * g))
    calc
      _ = ∫ h : H, a (h.val * g) ∂μH.inv := by
        simpa only [MeasurableEquiv.inv_apply, Subgroup.coe_inv, ← inv_def] using hi.symm
      _ = 1 := ha g ⟨g, hg, rfl⟩
  calc
    (∫ g, f g ∂μG) = ∫ g, f g * (∫ h : H, a (h.val⁻¹ * g) ∂μH) ∂μG := by
      apply integral_congr_ae
      filter_upwards [] with g
      by_cases hg : g ∈ tsupport f
      · rw [ha' g hg, mul_one]
      · rw [image_eq_zero_of_notMem_tsupport hg, zero_mul]
    _ = ∫ g, (∫ h : H, f (h.val * g) ∂μH) * a g ∂μG :=
      kernel_fubini H hH μG μH f a
    _ = 0 := by simp [hf]

/-- Vanishing of every actual subgroup average forces the ambient Haar integral to vanish. -/
theorem realAveragingKernelIntegralZero : RealAveragingKernelIntegralZero.{u} :=
  kernel_zero_of_normalization realQuotientCompactNormalization

end Langlands.QuotientIntegration
