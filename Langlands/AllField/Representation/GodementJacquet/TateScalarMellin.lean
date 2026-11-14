import Langlands.Representation.GodementJacquet.TateScalarMellin
import Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement
import Langlands.AllField.Representation.RankinSelberg.FunctionalEquationStatementSupplement
import Langlands.AllField.Representation.RankinSelberg.OneVariableMellinProof
/-! Actual scalar Mellin data retaining a common convergence half-plane. -/

noncomputable section

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding scalarMellinAnalyticData_finiteFunction
open Langlands.AllField.GodementJacquet

open _root_.MeasureTheory
open Langlands.HarmonicAnalysis
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankFunctionalEquationStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def finiteFunctionShellSeries iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow oneVariableMellin pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

universe uF

section Definitions



end Definitions

/-- The weighted normalized absolute value is an integer power of the spectral
point. Positivity of `q` fixes the logarithm branch. -/
private theorem mellin_natCast_zpow_cpow_eq (q : ℕ) (hq : 0 < q) (k : ℤ) (m : ℕ) (s : ℂ) :
    ((((q : ℝ) ^ (-k) : ℝ)) : ℂ) ^ ((m : ℂ) * s) = (spectralPoint q s ^ m) ^ k := by
  have harg : Complex.arg (q : ℂ) = 0 := by
    simpa only [Complex.ofReal_natCast] using
      Complex.arg_ofReal_of_nonneg (show 0 ≤ (q : ℝ) by positivity)
  rw [Complex.ofReal_zpow, Complex.ofReal_natCast,
    ← Complex.cpow_int_mul' (by simp [harg, Real.pi_pos])
      (by simpa only [harg, mul_zero] using Real.pi_pos.le),
    spectralPoint, ← zpow_natCast, ← zpow_mul, ← Complex.cpow_int_mul]
  congr 1
  push_cast
  ring

/-- Positive powers of the spectral point are small on a right half-plane. -/
private theorem mellin_exists_re_threshold {q : ℕ} (hq : 1 < q) {m : ℕ} (hm : 0 < m) {ρ : ℝ}
    (hρ : 0 < ρ) : ∃ c : ℝ, ∀ s : ℂ, c < s.re → ‖spectralPoint q s ^ m‖ < ρ := by
  set ρ1 := min ρ 1 with hρ1_def
  have hρ1 : 0 < ρ1 := lt_min hρ one_pos
  have hq0 : 0 < q := by omega
  have hlogq : 0 < Real.log q := Real.log_pos (by exact_mod_cast hq)
  refine ⟨-Real.log ρ1 / Real.log q, fun s hs => ?_⟩
  have hnorm : ‖spectralPoint q s‖ = (q : ℝ) ^ (-s.re) := by
    rw [spectralPoint, Complex.norm_natCast_cpow_of_pos hq0, Complex.neg_re]
  have ht : (q : ℝ) ^ (-s.re) < ρ1 := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast hq0), ← Real.lt_log_iff_exp_lt hρ1]
    rw [div_lt_iff₀ hlogq] at hs
    linarith
  have ht0 : 0 ≤ (q : ℝ) ^ (-s.re) := Real.rpow_nonneg (Nat.cast_nonneg q) _
  rw [norm_pow, hnorm]
  calc ((q : ℝ) ^ (-s.re)) ^ m ≤ (q : ℝ) ^ (-s.re) :=
        pow_le_of_le_one ht0 (ht.le.trans (min_le_right _ _)) hm.ne'
    _ < ρ1 := ht
    _ ≤ ρ := min_le_left _ _

private theorem mellin_normalizedAbs_cpow 
    {F : Type uF} [Field F] (T : LocalFieldData F)
    (a : Fˣ) (m : ℕ) (s : ℂ) :
    (T.normalizedAbs (a : F) : ℂ) ^ ((m : ℂ) * s) =
      (spectralPoint T.residueCardinality s ^ m) ^ T.ord (a : F) := by
  rw [T.normalizedAbs_of_ne_zero a.ne_zero,
    mellin_natCast_zpow_cpow_eq T.residueCardinality (by
      have := T.residueCardinality_gt_one
      omega)]

/-- The shell theorem supplies a uniform half-plane, and the published
one-variable Mellin theorem supplies rationality and a common denominator. -/
theorem scalarMellinAnalyticData_finiteFunction
    (F : Type uF) [Field F] (T : LocalFieldData F) :
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    letI : MeasurableSpace F := borel _
    letI : BorelSpace F := ⟨rfl⟩
    letI : MeasurableSpace Fˣ := borel _
    letI : BorelSpace Fˣ := ⟨rfl⟩
    ∀ (m : ℕ), 0 < m → ∀ (η : Fˣ → ℂ), Continuous η →
      FiniteDimensional ℂ (Submodule.span ℂ
        (Set.range fun b : Fˣ => fun a : Fˣ => η (b * a))) →
      ScalarMellinAnalyticData T.residueCardinality T.normalizedAbs
        (localMultiplicativeHaar F) η m := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  let : MeasurableSpace F := borel _
  let : BorelSpace F := ⟨rfl⟩
  let : MeasurableSpace Fˣ := borel _
  let : BorelSpace Fˣ := ⟨rfl⟩
  intro m hm η hη hfin
  obtain ⟨_, hrat, hden⟩ := oneVariableMellin F T m hm η hη hfin
  refine ⟨?_, hrat, hden⟩
  obtain ⟨π, E, B, _, hB, htests⟩ := finiteFunctionShellSeries F T η hη hfin
  have hBpos : 0 < B := lt_of_lt_of_le zero_lt_one hB
  obtain ⟨c, hc⟩ := mellin_exists_re_threshold T.residueCardinality_gt_one hm
    (one_div_pos.mpr hBpos)
  refine ⟨c, fun Φ s hs => ?_⟩
  obtain ⟨L, N, _, _, _, hI⟩ := htests Φ
  have hz : spectralPoint T.residueCardinality s ^ m ≠ 0 :=
    pow_ne_zero m (spectralPoint_ne_zero T.residueCardinality_gt_one s)
  have hsmall : B * ‖spectralPoint T.residueCardinality s ^ m‖ < 1 := by
    have h := (lt_div_iff₀ hBpos).mp (hc s hs)
    nlinarith
  change Integrable (fun a : Fˣ =>
    Φ (a : F) * η a *
      (T.normalizedAbs (a : F) : ℂ) ^ ((m : ℂ) * s)) _
  simp_rw [mellin_normalizedAbs_cpow T]
  exact (hI _ hz hsmall).1

end Langlands.AllField.GodementJacquet
