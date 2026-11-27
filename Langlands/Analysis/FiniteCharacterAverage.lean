import Mathlib.Analysis.Complex.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Topology.ContinuousMap.Compact

/-! # Character-weighted averages for finite group translations -/

noncomputable section

open MeasureTheory

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis

universe uK uH

variable {K : Type uK} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
  {H : Type uH} [Group H] [Fintype H]
  (s : H →* K) (χ : H →* ℂˣ)

/-- Average left translates of a continuous function with the supplied character weights. -/
def finiteCharacterAverage (ψ : C(K, ℂ)) : C(K, ℂ) :=
  (Fintype.card H : ℂ)⁻¹ • ∑ a : H, (χ a : ℂ) •
    ψ.comp ⟨fun x => s a * x, continuous_const.mul continuous_id⟩

theorem finiteCharacterAverage_apply (ψ : C(K, ℂ)) (x : K) :
    finiteCharacterAverage s χ ψ x =
      (Fintype.card H : ℂ)⁻¹ * ∑ a : H, (χ a : ℂ) * ψ (s a * x) := by
  simp only [finiteCharacterAverage, ContinuousMap.smul_apply, ContinuousMap.sum_apply,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, smul_eq_mul]

private theorem card_pos : 0 < Fintype.card H :=
  Fintype.card_pos_iff.mpr ⟨(1 : H)⟩

private theorem inv_card_mul_sum_const (c : ℂ) :
    (Fintype.card H : ℂ)⁻¹ * (∑ _ : H, c) = c := by
  have h : (Fintype.card H : ℂ) ≠ 0 := by exact_mod_cast card_pos (H := H) |>.ne'
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ h, one_mul]

/-- The characters of finite groups have unit absolute value. -/
theorem norm_finiteCharacter (a : H) : ‖(χ a : ℂ)‖ = 1 := by
  have ha : (χ a : ℂ) ^ orderOf a = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, pow_orderOf_eq_one, map_one, Units.val_one]
  have h := congrArg norm ha
  rw [norm_pow, norm_one] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (orderOf_pos a).ne').mp h

/-- The projected function transforms on the left by the inverse character. -/
theorem finiteCharacterAverage_covariant (ψ : C(K, ℂ)) (a : H) (x : K) :
    finiteCharacterAverage s χ ψ (s a * x) =
      (χ a : ℂ)⁻¹ * finiteCharacterAverage s χ ψ x := by
  have h : (∑ b : H, (χ b : ℂ) * ψ (s b * (s a * x))) =
      (χ a : ℂ)⁻¹ * ∑ b : H, (χ b : ℂ) * ψ (s b * x) := by
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.mulRight a) _ _ fun b => ?_
    change (χ b : ℂ) * ψ (s b * (s a * x)) =
      (χ a : ℂ)⁻¹ * ((χ (b * a) : ℂ) * ψ (s (b * a) * x))
    rw [map_mul χ, Units.val_mul, map_mul s, ← mul_assoc (s b) (s a) x]
    field_simp [Units.ne_zero (χ a)]
  simp only [finiteCharacterAverage_apply, h]
  ring

theorem finiteCharacterAverage_apply_of_terms_eq (ψ : C(K, ℂ)) (x : K) (c : ℂ)
    (hc : ∀ a : H, (χ a : ℂ) * ψ (s a * x) = c) : finiteCharacterAverage s χ ψ x = c := by
  simp only [finiteCharacterAverage_apply, hc]
  exact inv_card_mul_sum_const c

variable [CompactSpace K]

private theorem norm_average_sum_le (z : H → ℂ) {B : ℝ} (hz : ∀ a, ‖z a‖ ≤ B) :
    ‖(Fintype.card H : ℂ)⁻¹ * ∑ a : H, z a‖ ≤ B := by
  have hcard : 0 < (Fintype.card H : ℝ) := by exact_mod_cast card_pos (H := H)
  calc
    _ = (Fintype.card H : ℝ)⁻¹ * ‖∑ a : H, z a‖ := by
      rw [norm_mul, norm_inv, Complex.norm_natCast]
    _ ≤ (Fintype.card H : ℝ)⁻¹ * ∑ a : H, ‖z a‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hcard.le)
    _ ≤ (Fintype.card H : ℝ)⁻¹ * ∑ _ : H, B :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun a _ => hz a) (inv_nonneg.mpr hcard.le)
    _ = B := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ hcard.ne', one_mul]

theorem norm_finiteCharacterAverage_le (ψ : C(K, ℂ)) :
    ‖finiteCharacterAverage s χ ψ‖ ≤ ‖ψ‖ := by
  apply (ContinuousMap.norm_le _ (norm_nonneg _)).mpr
  intro x
  rw [finiteCharacterAverage_apply]
  apply norm_average_sum_le
  intro a
  rw [norm_mul, norm_finiteCharacter χ, one_mul]
  exact ψ.norm_coe_le_norm _

omit [CompactSpace K] in
/-- Any uniform two-point estimate for the left translates is preserved by the average. -/
theorem norm_sub_finiteCharacterAverage_le (ψ : C(K, ℂ)) (x y : K) {B : ℝ}
    (hB : ∀ a : H, ‖ψ (s a * x) - ψ (s a * y)‖ ≤ B) :
    ‖finiteCharacterAverage s χ ψ x - finiteCharacterAverage s χ ψ y‖ ≤ B := by
  rw [finiteCharacterAverage_apply, finiteCharacterAverage_apply, ← mul_sub,
    ← Finset.sum_sub_distrib]
  apply norm_average_sum_le
  intro a
  rw [← mul_sub, norm_mul, norm_finiteCharacter χ, one_mul]
  exact hB a

variable [MeasurableSpace K] [BorelSpace K] [MeasurableMul K]
  (μ : Measure K) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant]

/-- Pairing against a left-character kernel depends only on the inverse-character part
of the test. -/
theorem integral_mul_finiteCharacterAverage (κ ψ : C(K, ℂ))
    (hκ : ∀ (a : H) (x : K), κ (s a * x) = (χ a : ℂ) * κ x) :
    (∫ x, κ x * finiteCharacterAverage s χ ψ x ∂μ) = ∫ x, κ x * ψ x ∂μ := by
  have he (x : K) : κ x * finiteCharacterAverage s χ ψ x =
      (Fintype.card H : ℂ)⁻¹ * ∑ a : H, κ (s a * x) * ψ (s a * x) := by
    rw [finiteCharacterAverage_apply, mul_left_comm (κ x), Finset.mul_sum]
    refine congrArg ((Fintype.card H : ℂ)⁻¹ * ·) (Finset.sum_congr rfl fun a _ => ?_)
    rw [hκ]
    ring
  simp_rw [he]
  rw [integral_const_mul, integral_finsetSum]
  · simp_rw [integral_mul_left_eq_self (fun x => κ x * ψ x)]
    exact inv_card_mul_sum_const _
  · intro a _
    have hc : Continuous (fun x : K => κ (s a * x) * ψ (s a * x)) :=
      (κ.continuous.mul ψ.continuous).comp (continuous_const.mul continuous_id)
    exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The finite character projection is contractive and its bilinear integral pairing
with a left-character kernel agrees with the original pairing. -/
def FiniteCharacterAverageStatement : Prop :=
  ∀ (K : Type uK) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K]
    [MeasurableSpace K] [BorelSpace K] [MeasurableMul K]
    (H : Type uH) [Group H] [Fintype H] (s : H →* K) (χ : H →* ℂˣ)
    (μ : Measure K) [IsFiniteMeasure μ] [μ.IsMulLeftInvariant] (ψ : C(K, ℂ)),
    ‖finiteCharacterAverage s χ ψ‖ ≤ ‖ψ‖ ∧
      (∀ (a : H) (x : K), finiteCharacterAverage s χ ψ (s a * x) =
        (χ a : ℂ)⁻¹ * finiteCharacterAverage s χ ψ x) ∧
      ∀ κ : C(K, ℂ), (∀ (a : H) (x : K), κ (s a * x) = (χ a : ℂ) * κ x) →
        (∫ x, κ x * finiteCharacterAverage s χ ψ x ∂μ) = ∫ x, κ x * ψ x ∂μ

theorem finiteCharacterAverage_spec : FiniteCharacterAverageStatement.{uK, uH} :=
  fun _ _ _ _ _ _ _ _ _ _ _ s χ μ _ _ ψ => ⟨norm_finiteCharacterAverage_le s χ ψ,
    finiteCharacterAverage_covariant s χ ψ, fun κ hκ =>
      integral_mul_finiteCharacterAverage s χ μ κ ψ hκ⟩

end Langlands.Analysis
