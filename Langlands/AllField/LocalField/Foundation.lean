import Langlands.LocalField.LocalFieldArithmetic
import Langlands.LocalField.LocalUniformizer
import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology
import Mathlib.Topology.MetricSpace.Basic

/-!
# Normalized absolute value of supplied local-field data: topology

Arithmetic and topological laws of `LocalFieldData.normalizedAbs` beyond those
of `Langlands.LocalField.LocalFieldArithmetic`, for every nonarchimedean local
field (any characteristic). They replace the p-adic lemmas of
`Langlands.LocalField.Normalization.Proof` that the all-field port uses.
-/

open scoped WithZero Topology
open Filter

namespace Langlands.LocalFieldData

universe u
variable {F : Type u} [Field F] (T : LocalFieldData F)

theorem normalizedAbs_eq_zero_iff (x : F) :
    T.normalizedAbs x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    exact (T.normalizedAbs_pos hx).ne' h
  · rintro rfl
    exact T.normalizedAbs_zero

theorem normalizedAbs_le_one_iff_mem_integers (x : F) :
    T.normalizedAbs x ≤ 1 ↔ x ∈ T.Integers := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  by_cases hx : x = 0
  · simp [hx, T.normalizedAbs_zero]
  have h := T.normalizedAbs_le_iff_of_ne_zero hx (one_ne_zero : (1 : F) ≠ 0)
  rw [T.normalizedAbs_one, map_one] at h
  rw [h]
  change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)
      (ValuativeRel.valuation F x) ≤ 1 ↔
    ValuativeRel.valuation F x ≤ 1
  rw [← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F)]
  exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).strictMono.le_iff_le

private theorem one_lt_q : (1 : ℝ) < T.residueCardinality := by
  exact_mod_cast T.residueCardinality_gt_one

/-- Strict bounds by integer powers of the residue cardinality are valuation bounds. -/
theorem normalizedAbs_lt_zpow_iff (x : F) (m : ℤ) :
    T.normalizedAbs x < (T.residueCardinality : ℝ) ^ m ↔
      T.discreteValuation x < WithZero.exp m := by
  by_cases hx : x = 0
  · subst hx
    simp only [T.normalizedAbs_zero, map_zero, WithZero.exp_pos, iff_true]
    exact zpow_pos (zero_lt_one.trans T.one_lt_q) m
  have hv : T.discreteValuation x ≠ 0 := T.discreteValuation.ne_zero_iff.mpr hx
  rw [T.normalizedAbs_of_ne_zero hx, zpow_lt_zpow_iff_right₀ T.one_lt_q, ord, neg_neg,
    WithZero.log_lt_iff_lt_exp hv]

theorem normalizedAbs_neg (x : F) : T.normalizedAbs (-x) = T.normalizedAbs x := by
  have h1 : T.normalizedAbs (-1) = 1 := by
    have hsq : T.normalizedAbs (-1) * T.normalizedAbs (-1) = 1 := by
      rw [← T.normalizedAbs_mul, neg_one_mul, neg_neg, T.normalizedAbs_one]
    have hn := T.normalizedAbs_nonneg (-1)
    nlinarith [T.normalizedAbs_nonneg (-1)]
  rw [neg_eq_neg_one_mul, T.normalizedAbs_mul, h1, one_mul]

theorem normalizedAbs_sub_le (x y : F) :
    |T.normalizedAbs x - T.normalizedAbs y| ≤ T.normalizedAbs (x - y) := by
  have h1 : T.normalizedAbs x ≤ T.normalizedAbs (x - y) + T.normalizedAbs y := by
    calc T.normalizedAbs x = T.normalizedAbs ((x - y) + y) := by rw [sub_add_cancel]
      _ ≤ max (T.normalizedAbs (x - y)) (T.normalizedAbs y) := T.normalizedAbs_add_le_max _ _
      _ ≤ _ := max_le (le_add_of_nonneg_right (T.normalizedAbs_nonneg _))
          (le_add_of_nonneg_left (T.normalizedAbs_nonneg _))
  have h2 : T.normalizedAbs y ≤ T.normalizedAbs (x - y) + T.normalizedAbs x := by
    calc T.normalizedAbs y = T.normalizedAbs (-(x - y) + x) := by ring_nf
      _ ≤ max (T.normalizedAbs (-(x - y))) (T.normalizedAbs x) := T.normalizedAbs_add_le_max _ _
      _ ≤ _ := by
        rw [T.normalizedAbs_neg]
        exact max_le (le_add_of_nonneg_right (T.normalizedAbs_nonneg _))
          (le_add_of_nonneg_left (T.normalizedAbs_nonneg _))
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The normalized-absolute-value balls form a neighbourhood basis. -/
theorem hasBasis_nhds_normalizedAbs (a : F) :
    letI := T.topology
    (𝓝 a).HasBasis (fun ε : ℝ => 0 < ε) (fun ε => {x | T.normalizedAbs (x - a) < ε}) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let e := IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F
  have hdv (x : F) : T.discreteValuation x = e (ValuativeRel.valuation F x) := rfl
  refine (IsValuativeTopology.hasBasis_nhds' a).to_hasBasis ?_ ?_
  · intro γ hγ
    have heγ : e γ ≠ 0 := by simpa using hγ
    refine ⟨(T.residueCardinality : ℝ) ^ (WithZero.log (e γ)),
      zpow_pos (zero_lt_one.trans T.one_lt_q) _, ?_⟩
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [T.normalizedAbs_lt_zpow_iff, WithZero.exp_log heγ, hdv] at hx
    exact e.strictMono.lt_iff_lt.mp hx
  · intro ε hε
    obtain ⟨m, hm⟩ : ∃ m : ℤ, (T.residueCardinality : ℝ) ^ m < ε := by
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε (inv_lt_one_of_one_lt₀ T.one_lt_q)
      exact ⟨-(n : ℤ), by rwa [zpow_neg, zpow_natCast, ← inv_pow]⟩
    refine ⟨e.symm (WithZero.exp m), by simp, ?_⟩
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    refine lt_trans ?_ hm
    rw [T.normalizedAbs_lt_zpow_iff, hdv]
    have := e.strictMono hx
    simpa using this

/-- The normalized absolute value is continuous for the supplied topology. -/
theorem continuous_normalizedAbs :
    letI := T.topology
    Continuous T.normalizedAbs := by
  let := T.topology
  rw [continuous_iff_continuousAt]
  intro a
  refine ((T.hasBasis_nhds_normalizedAbs a).tendsto_iff Metric.nhds_basis_ball).mpr ?_
  intro ε hε
  refine ⟨ε, hε, fun x hx => ?_⟩
  simp only [Set.mem_ofPred_eq] at hx
  rw [Metric.mem_ball, Real.dist_eq]
  exact lt_of_le_of_lt (T.normalizedAbs_sub_le x a) hx

/-- Open normalized-absolute-value balls form a basis of the supplied topology. -/
theorem normalizedAbs_balls_basis :
    letI := T.topology
    TopologicalSpace.IsTopologicalBasis
      {U : Set F | ∃ (a : F) (ε : ℝ),
        0 < ε ∧ U = {x | T.normalizedAbs (x - a) < ε}} := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have : IsTopologicalAddGroup F := inferInstance
  refine TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds ?_ ?_
  · rintro U ⟨a, ε, _, rfl⟩
    exact isOpen_lt (T.continuous_normalizedAbs.comp (continuous_id.sub continuous_const))
      continuous_const
  · intro a U ha hU
    obtain ⟨ε, hε, hsub⟩ := (T.hasBasis_nhds_normalizedAbs a).mem_iff.mp (hU.mem_nhds ha)
    refine ⟨{x | T.normalizedAbs (x - a) < ε}, ⟨a, ε, hε, rfl⟩, ?_, hsub⟩
    simpa [T.normalizedAbs_zero] using hε

/-- The field is Hausdorff for the supplied topology. -/
theorem fieldT2 :
    letI := T.topology
    T2Space F := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact HarmonicAnalysis.GeneralLocalField.t2Space F

/-- The supplied field topology is sigma compact. -/
theorem sigmaCompactSpace : letI := T.topology; SigmaCompactSpace F := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact HarmonicAnalysis.GeneralLocalField.sigmaCompactSpace F

/-- The supplied field topology is second countable. -/
theorem secondCountableTopology : letI := T.topology; SecondCountableTopology F := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact HarmonicAnalysis.GeneralLocalField.secondCountableTopology F

/-- The supplied field topology is pseudometrizable. -/
theorem pseudoMetrizableSpace : letI := T.topology; TopologicalSpace.PseudoMetrizableSpace F := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact HarmonicAnalysis.GeneralLocalField.pseudoMetrizableSpace F

/-- The integer ring of the supplied valuation is compact. -/
theorem isCompact_integers : letI := T.topology; IsCompact (T.Integers : Set F) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact IsNonarchimedeanLocalField.isCompact_closedBall F 1

/-- The integer ring of the supplied valuation is open. -/
theorem isOpen_integers : letI := T.topology; IsOpen (T.Integers : Set F) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  exact (ValuativeRel.valuation F).isOpen_integer

/-- Every additive Haar measure for the supplied Borel topology is regular. -/
theorem haarMeasure_regular :
    letI := T.topology
    ∀ [MeasurableSpace F] [BorelSpace F]
      (μ : MeasureTheory.Measure F) [μ.IsAddHaarMeasure], μ.Regular := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  intro _ _ μ _
  exact HarmonicAnalysis.GeneralLocalField.haarMeasure_regular F μ

end Langlands.LocalFieldData
