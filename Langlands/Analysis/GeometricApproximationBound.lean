import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Global bounds from filtered bounds and geometric approximation -/

noncomputable section

open Filter
open scoped Topology

set_option autoImplicit false

namespace Langlands.Analysis

universe uV uE

/-- A linear map with geometrically growing bounds on a filtration is bounded by the
original norm and the error scale of a faster approximation that preserves the filtration. -/
def GeometricApproximationBoundStatement : Prop :=
  ∀ (V : Type uV) [NormedAddCommGroup V] [NormedSpace ℂ V]
    (E : Type uE) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (W : ℕ → Submodule ℂ V) (T : V →ₗ[ℂ] E) (P : ℕ → V → V)
    (p : V → ℝ) (C a b : ℝ),
    Monotone W → (∀ v : V, ∃ j, v ∈ W j) → (∀ v, 0 ≤ p v) →
    0 ≤ C → 0 ≤ a → 1 ≤ b → a * b < 1 →
    (∀ j, ∀ v ∈ W j, ‖T v‖ ≤ C * b ^ j * ‖v‖) →
    (∀ j v, P j v ∈ W j) → (∀ j l, ∀ v ∈ W l, P j v ∈ W l) →
    (∀ j v, ‖P j v - v‖ ≤ a ^ j * p v) →
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ v, ‖T v‖ ≤ C' * (‖v‖ + p v)

/-- Bound the differences at consecutive scales and sum their geometric majorant.
Convergence after applying the map follows from the bound on a single fixed layer. -/
theorem geometricApproximationBound : GeometricApproximationBoundStatement.{uV, uE} := by
  intro V _ _ E _ _ W T P p C a b hW hcover hp hC ha hb hq hT hP hPres hError
  let q := a * b
  have hb₀ : 0 ≤ b := zero_le_one.trans hb
  have hq₀ : 0 ≤ q := mul_nonneg ha hb₀
  have ha₁ : a < 1 := (le_mul_of_one_le_right ha hb).trans_lt hq
  let A := b * (1 + a)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  let B := 1 + A / (1 - q)
  have hgap : 0 < 1 - q := sub_pos.mpr hq
  have hB : 1 ≤ B := le_add_of_nonneg_right (div_nonneg hA hgap.le)
  refine ⟨C * B, mul_nonneg hC (zero_le_one.trans hB), fun v => ?_⟩
  have hbase : ‖T (P 0 v)‖ ≤ C * (‖v‖ + p v) := by
    have hNorm : ‖P 0 v‖ ≤ ‖v‖ + p v := calc
      ‖P 0 v‖ = ‖v + (P 0 v - v)‖ := by rw [add_sub_cancel]
      _ ≤ ‖v‖ + ‖P 0 v - v‖ := norm_add_le _ _
      _ ≤ _ := add_le_add le_rfl (by simpa only [pow_zero, one_mul] using hError 0 v)
    exact (by simpa only [pow_zero, mul_one] using hT 0 (P 0 v) (hP 0 v) :
      ‖T (P 0 v)‖ ≤ C * ‖P 0 v‖).trans (mul_le_mul_of_nonneg_left hNorm hC)
  have hDifference (j : ℕ) :
      ‖T (P (j + 1) v - P j v)‖ ≤ C * A * p v * q ^ j := by
    have hj : P j v ∈ W (j + 1) := hW (Nat.le_succ j) (hP _ _)
    have hΔ : P (j + 1) v - P j v ∈ W (j + 1) := (W _).sub_mem (hP _ _) hj
    have hNorm : ‖P (j + 1) v - P j v‖ ≤ (1 + a) * a ^ j * p v := calc
      _ = ‖(P (j + 1) v - v) - (P j v - v)‖ := by rw [sub_sub_sub_cancel_right]
      _ ≤ ‖P (j + 1) v - v‖ + ‖P j v - v‖ := norm_sub_le _ _
      _ ≤ a ^ (j + 1) * p v + a ^ j * p v := add_le_add (hError _ _) (hError _ _)
      _ = _ := by rw [pow_succ]; ring
    calc
      _ ≤ C * b ^ (j + 1) * ‖P (j + 1) v - P j v‖ := hT _ _ hΔ
      _ ≤ C * b ^ (j + 1) * ((1 + a) * a ^ j * p v) :=
        mul_le_mul_of_nonneg_left hNorm (by positivity)
      _ = _ := by simp only [q, A, mul_pow, pow_succ b]; ring
  have htel (N : ℕ) : T (P N v) = T (P 0 v) +
      ∑ j ∈ Finset.range N, T (P (j + 1) v - P j v) := by
    induction N with
    | zero => simp
    | succ N ih =>
      rw [Finset.sum_range_succ, map_sub, ← add_assoc, ← ih]
      abel
  have hgeom (N : ℕ) : ∑ j ∈ Finset.range N, q ^ j ≤ (1 - q)⁻¹ := by
    rw [← tsum_geometric_of_lt_one hq₀ hq]
    exact (summable_geometric_of_lt_one hq₀ hq).sum_le_tsum _
      (fun j _ => pow_nonneg hq₀ _)
  have hfinite (N : ℕ) : ‖T (P N v)‖ ≤ (C * B) * (‖v‖ + p v) := calc
    _ ≤ ‖T (P 0 v)‖ + ∑ j ∈ Finset.range N, ‖T (P (j + 1) v - P j v)‖ := by
      rw [htel]
      exact (norm_add_le _ _).trans (add_le_add le_rfl (norm_sum_le _ _))
    _ ≤ C * (‖v‖ + p v) + ∑ j ∈ Finset.range N, C * A * p v * q ^ j :=
      add_le_add hbase (Finset.sum_le_sum fun j _ => hDifference j)
    _ ≤ C * (‖v‖ + p v) + C * A * p v * (1 - q)⁻¹ := by
      rw [← Finset.mul_sum]
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left (hgeom N) (mul_nonneg (mul_nonneg hC hA) (hp v)))
    _ = C * ‖v‖ + C * B * p v := by simp only [B, div_eq_mul_inv]; ring
    _ ≤ _ := by
      rw [mul_add (C * B) ‖v‖ (p v)]
      exact add_le_add (mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right hC hB) (norm_nonneg v)) le_rfl
  obtain ⟨l, hl⟩ := hcover v
  have hdist (j : ℕ) : dist (T (P j v)) (T v) ≤ (C * b ^ l * p v) * a ^ j := by
    rw [dist_eq_norm, ← map_sub]
    calc
      _ ≤ C * b ^ l * ‖P j v - v‖ := hT _ _ ((W l).sub_mem (hPres j l v hl) hl)
      _ ≤ C * b ^ l * (a ^ j * p v) := mul_le_mul_of_nonneg_left (hError _ _) (by positivity)
      _ = _ := by ring
  have hTendsto : Tendsto (fun j => T (P j v)) atTop (𝓝 (T v)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ => dist_nonneg) hdist
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one ha ha₁).const_mul (C * b ^ l * p v)
  exact le_of_tendsto (continuous_norm.continuousAt.tendsto.comp hTendsto)
    (Eventually.of_forall hfinite)

end Langlands.Analysis
