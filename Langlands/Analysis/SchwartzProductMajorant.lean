import Mathlib.Analysis.Distribution.SchwartzSpace.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-! # Product bounds for Schwartz kernels on finite coordinate spaces -/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Analysis

variable {ι F : Type*} [Fintype ι] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- A Schwartz function on finitely many coordinates is dominated by the
product of any fixed polynomial decay on each coordinate. -/
theorem exists_schwartz_norm_le_coordinate_decay (Φ : SchwartzMap (ι → F) ℂ) (p : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ι → F, ‖Φ x‖ ≤
      C * ∏ i, ((1 + ‖x i‖) ^ p)⁻¹ := by
  let N := Fintype.card ι * p
  let C := (2 : ℝ) ^ N *
    (Finset.Iic (N, 0)).sup (fun x => SchwartzMap.seminorm ℝ x.1 x.2) Φ
  refine ⟨C, by dsimp [C]; positivity, fun x => ?_⟩
  rw [Finset.prod_inv_distrib, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have hprod : (∏ i, (1 + ‖x i‖) ^ p) ≤ (1 + ‖x‖) ^ N := by
    calc
      _ ≤ ∏ _i : ι, (1 + ‖x‖) ^ p := by
        gcongr with i
        exact norm_le_pi_norm x i
      _ = _ := by
        rw [Finset.prod_const, Finset.card_univ, ← pow_mul]
        simp only [N, mul_comm]
  have hnorm : (1 + ‖x‖) ^ N * ‖Φ x‖ ≤ C := by
    simpa only [C, norm_iteratedFDeriv_zero] using
      SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (N, 0)) le_rfl le_rfl Φ x
  calc
    _ ≤ ‖Φ x‖ * (1 + ‖x‖) ^ N := mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
    _ ≤ _ := (mul_comm _ _).trans_le hnorm

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F]

/-- Coordinate weights whose norms become integrable after polynomial
damping are integrable against a Schwartz test on their product. -/
theorem integrable_schwartz_mul_coordinateWeights (Φ : SchwartzMap (ι → F) ℂ)
    (μ : ι → Measure F) [∀ i, SigmaFinite (μ i)] (κ : ι → F → ℂ)
    (hκ : ∀ i, Measurable (κ i)) (p : ℕ)
    (hI : ∀ i, Integrable (fun x => ‖κ i x‖ * ((1 + ‖x‖) ^ p)⁻¹) (μ i)) :
    Integrable (fun x : ι → F => Φ x * ∏ i, κ i (x i)) (Measure.pi μ) := by
  obtain ⟨C, _, hC⟩ := exists_schwartz_norm_le_coordinate_decay Φ p
  have hmeas : Measurable (fun x : ι → F => Φ x * ∏ i, κ i (x i)) :=
    Φ.continuous.measurable.mul
      (Finset.measurable_prod _ (fun i _ => (hκ i).comp (measurable_pi_apply i)))
  have hprod := Integrable.fintype_prod hI
  refine (hprod.const_mul C).mono' hmeas.aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [norm_mul, Complex.norm_prod, Finset.prod_mul_distrib]
  calc
    _ ≤ (C * ∏ i, ((1 + ‖x i‖) ^ p)⁻¹) * (∏ i, ‖κ i (x i)‖) :=
      mul_le_mul_of_nonneg_right (hC x) (by positivity)
    _ = _ := by ring

end Langlands.Analysis
