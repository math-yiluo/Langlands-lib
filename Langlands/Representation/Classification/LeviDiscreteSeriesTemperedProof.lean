import Langlands.Representation.Classification.DiscreteSeriesJacquetStatement
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator
import Mathlib.MeasureTheory.Function.L1Space.Integrable

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace Langlands

universe uF uW

private theorem bounded_of_memLp_two_right_invariant
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] {f : G → ℝ}
    (hf : MemLp f 2 μ) (S : Set G) (hS : IsOpen S) (hne : S.Nonempty)
    (hinv : ∀ q k, k ∈ S → f (q * k) = f q) :
    ∃ C : ℝ, ∀ q, ‖f q‖ ≤ C := by
  let d : ℝ≥0∞ := μ S ^ (1 / (2 : ℝ))
  have hd : d ≠ 0 := by
    dsimp [d]
    exact ne_of_gt (ENNReal.rpow_pos_of_nonneg (hS.measure_pos μ hne) (by positivity))
  let B := eLpNorm f 2 μ / d
  have hB : B ≠ ∞ := (ENNReal.div_lt_top hf.eLpNorm_ne_top hd).ne
  refine ⟨B.toReal, fun q => ?_⟩
  have hbound : ‖f q‖ₑ * d ≤ eLpNorm f 2 μ := by
    have heq : S.indicator (fun _ : G => f q) = S.indicator (f ∘ (q * ·)) := by
      ext k
      by_cases hk : k ∈ S
      · simp [hk, hinv q k hk]
      · simp [hk]
    calc
      ‖f q‖ₑ * d = eLpNorm (S.indicator (fun _ : G => f q)) 2 μ := by
        rw [eLpNorm_indicator_const hS.measurableSet.nullMeasurableSet (by norm_num)
          (by norm_num)]
        norm_num [d]
      _ = eLpNorm (S.indicator (f ∘ (q * ·))) 2 μ := congrArg (fun g => eLpNorm g 2 μ) heq
      _ ≤ eLpNorm (f ∘ (q * ·)) 2 μ := eLpNorm_indicator_le _ hS.measurableSet
      _ = eLpNorm f 2 μ :=
        eLpNorm_comp_measurePreserving hf.aestronglyMeasurable (measurePreserving_mul_left μ q)
  have hle : ‖f q‖ₑ ≤ B :=
    (ENNReal.le_div_iff_mul_le (.inl hd) (.inr hf.eLpNorm_ne_top)).2 hbound
  simpa using ENNReal.toReal_mono hB hle

private theorem memLp_two_add_of_bounded
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    (hf : MemLp f 2 μ) (C : ℝ) (hC : ∀ x, ‖f x‖ ≤ C)
    (ε : ℝ) (hε : 0 < ε) : MemLp f (ENNReal.ofReal (2 + ε)) μ := by
  have hp : 0 < 2 + ε := by linarith
  apply (integrable_norm_rpow_iff hf.aestronglyMeasurable (by positivity) ENNReal.ofReal_ne_top).mp
  rw [ENNReal.toReal_ofReal hp.le]
  have hi : Integrable (fun x => ‖f x‖ ^ (2 : ℝ)) μ := by
    simpa using hf.integrable_norm_rpow (by norm_num) (by norm_num)
  refine (hi.const_mul (C ^ ε)).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (hf.aestronglyMeasurable.norm.aemeasurable.pow_const _).aestronglyMeasurable
  · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num) hε.le]
    rw [mul_comm (C ^ ε)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (norm_nonneg _) (hC x) hε.le)
      (Real.rpow_nonneg (norm_nonneg _) _)

/-- Smooth square-integrable coefficients on the actual central quotient are
bounded by their common open-stabilizer translates, hence lie in every L^(2+ε). -/
theorem isTemperedModCenter_of_squareIntegrable
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    {ρ : Representation ℂ G V} (μ : Measure (G ⧸ Subgroup.center G))
    [μ.IsHaarMeasure] (hρ : IsSquareIntegrableModCenter ρ μ) :
    IsTemperedModCenter ρ μ := by
  obtain ⟨ha, c, hc⟩ := hρ
  refine ⟨ha, c, fun ℓ v ε hε => ?_⟩
  obtain ⟨K, hv⟩ := ha.1 v
  let S : Set (G ⧸ Subgroup.center G) := QuotientGroup.mk '' (K : Set G)
  have hS : IsOpen S := QuotientGroup.isOpenMap_coe _ K.isOpen
  have hne : S.Nonempty := ⟨QuotientGroup.mk 1, 1, K.one_mem, rfl⟩
  have hinv : ∀ q k, k ∈ S → c.coefficientNorm ℓ v (q * k) = c.coefficientNorm ℓ v q := by
    intro q k hk
    obtain ⟨a, haK, rfl⟩ := hk
    induction q using Quotient.inductionOn with
    | h g =>
      change ‖ℓ.val (ρ (g * a) v)‖ = ‖ℓ.val (ρ g v)‖
      have hva : ρ a v = v := hv ⟨a, haK⟩
      rw [map_mul, Module.End.mul_apply, hva]
  obtain ⟨C, hC⟩ := bounded_of_memLp_two_right_invariant μ (hc ℓ v) S hS hne hinv
  exact memLp_two_add_of_bounded (hc ℓ v) C hC ε hε

/-- Square-integrable representations of every actual GL block Levi are tempered
for the same Haar measure, with independent field and representation universes. -/
theorem glLeviDiscreteSeriesTempered : GLLeviDiscreteSeriesTemperedStatement.{uF, uW} := by
  intro p hp F T
  let := T.topology
  intro n hn B
  let := T.leviTopologicalGroup B
  dsimp only
  intro mQ bQ μ hμ W aW mW σ _hσ hs
  exact isTemperedModCenter_of_squareIntegrable μ hs

end Langlands
