import Langlands.Analysis.Local.QuotientMeasurePrerequisites
import Langlands.Analysis.Local.QuotientAverageReal
import Mathlib.Topology.UrysohnsLemma
import Mathlib.Topology.Order.Compact

/-!
# Compact normalization and positive lifting for real quotient averages
-/

noncomputable section

namespace Langlands.QuotientIntegration

open MeasureTheory MeasureTheory.Measure Set
open scoped CompactlySupported

universe u

private theorem quotient_mk_subgroup_mul {G : Type u} [Group G]
    (H : Subgroup G) (h : H) (g : G) :
    Quotient.mk (QuotientGroup.rightRel H) (h.val * g) =
      Quotient.mk (QuotientGroup.rightRel H) g := by
  apply Quotient.sound
  apply QuotientGroup.rightRel_apply.mpr
  simp [mul_inv_rev]

/-- Nonnegative compact normalization for the actual real fiber integral. -/
theorem realQuotientCompactNormalization : RealQuotientCompactNormalization.{u} := by
  intro G _ _ _ _ _ H hH _ _ μH _ _ _ K hK
  obtain ⟨C, hC, hCK⟩ := leftQuotient_exists_isCompact_image H hH hK
  obtain ⟨b, hbC, hbc, _, hb⟩ :=
    exists_continuousMap_one_of_isCompact_subset_isOpen hC isOpen_univ (subset_univ C)
  let b₀ : C_c(G, ℝ) := ⟨b, hbc⟩
  let A := quotientAverageReal H μH b₀
  have hAc : Continuous A := continuous_quotientAverageReal H hH μH b₀
  have hApos : ∀ q ∈ K, 0 < A q := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := hCK ▸ hq
    change 0 < ∫ h : H, b₀ (h.val * x) ∂μH
    apply integral_pos_of_integrable_nonneg_nonzero
      (b₀.continuous.comp (continuous_subtype_val.mul_const x))
      (integrable_subgroup_mul H hH μH b₀ x) (fun h => (hb (h.val * x)).1)
      (x := (1 : H))
    change b ((1 : H).val * x) ≠ 0
    simpa only [OneMemClass.coe_one, one_mul, hbC hx, Pi.one_apply] using
      (one_ne_zero : (1 : ℝ) ≠ 0)
  obtain ⟨ε, hε, hεA⟩ := hK.exists_forall_le' hAc.continuousOn hApos
  let d : G → ℝ := fun g => max ε (A (leftQuotientMap H g))
  have hd : Continuous d := continuous_const.max (hAc.comp continuous_quotient_mk')
  have hdpos : ∀ g, 0 < d g := fun g => lt_of_lt_of_le hε (le_max_left _ _)
  let f : C_c(G, ℝ) :=
    { toFun := fun g => b₀ g / d g
      continuous_toFun := b₀.continuous.div hd (fun g => ne_of_gt (hdpos g))
      hasCompactSupport' := by
        simpa only [Pi.mul_def, div_eq_mul_inv] using
          (b₀.hasCompactSupport.mul_right (f' := fun g => (d g)⁻¹)) }
  refine ⟨f, fun g => div_nonneg (hb g).1 (hdpos g).le, ?_⟩
  intro g hg
  have hdf (h : H) : d (h.val * g) = d g := by
    simp only [d, leftQuotientMap_apply, quotient_mk_subgroup_mul]
  change (∫ h : H, b₀ (h.val * g) / d (h.val * g) ∂μH) = 1
  simp_rw [hdf]
  rw [integral_div]
  change A (leftQuotientMap H g) / max ε (A (leftQuotientMap H g)) = 1
  change A (Quotient.mk _ g) / max ε (A (Quotient.mk _ g)) = 1
  rw [max_eq_right (hεA _ hg)]
  exact div_self (ne_of_gt (hApos _ hg))

/-- Every real quotient test function has a lift, preserving nonnegativity. -/
theorem realQuotientPositiveLifting : RealQuotientPositiveLifting.{u} := by
  intro G _ _ _ _ _ H hH _ _ μH _ _ _ φ
  obtain ⟨b, hb, hbK⟩ := realQuotientCompactNormalization H hH μH
    (tsupport φ) φ.hasCompactSupport
  let f : C_c(G, ℝ) :=
    { toFun := fun g => φ (leftQuotientMap H g) * b g
      continuous_toFun := (φ.continuous.comp continuous_quotient_mk').mul b.continuous
      hasCompactSupport' := b.hasCompactSupport.mul_left }
  refine ⟨f, ?_, fun hφ g => mul_nonneg (hφ _) (hb _)⟩
  intro g
  change (∫ h : H, φ (leftQuotientMap H (h.val * g)) * b (h.val * g) ∂μH) = _
  simp_rw [leftQuotientMap_apply, quotient_mk_subgroup_mul]
  rw [integral_const_mul]
  by_cases hg : Quotient.mk (QuotientGroup.rightRel H) g ∈ tsupport φ
  · rw [hbK g hg, mul_one]
  · rw [image_eq_zero_of_notMem_tsupport hg, zero_mul]

end Langlands.QuotientIntegration
