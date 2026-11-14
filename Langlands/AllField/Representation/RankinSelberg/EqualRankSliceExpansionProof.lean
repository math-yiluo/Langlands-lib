import Langlands.Representation.RankinSelberg.EqualRankSliceExpansionProof
import Langlands.AllField.Representation.RankinSelberg.EqualRankSliceExpansionStatement
/-!
# Proof of the conditional equal-rank determinant-series expansion

JPSS (1983), Section 4.2, (4.2.1)–(4.2.2), printed pages 406–407. For any measure on
the Borel structure of the actual quotient `N_(n+1) \ GL_(n+1)`, a globally integrable
function is the sum of its integrals over the determinant slices, and these slice
integrals are absolutely summable. Applied to the equal-rank integrand at a convergent
parameter, this gives slice integrability at zero and the absolutely summable expansion
`Ψ(s) = Σ_m Ψ^m (q^(-s))^m`.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement EqualRankSliceExpansionStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def equalRankSliceExpansion hasSum_setIntegral_determinantSlice iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable summable_norm_setIntegral_determinantSlice zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.HarmonicAnalysis
open _root_.MeasureTheory

universe uF

section Partition

variable {F : Type uF} [Field F] (T : LocalFieldData F) {n : ℕ}
variable (μ : letI := T.topology
  letI := borel (LeftUnipotentQuotient n F)
  Measure (LeftUnipotentQuotient n F))

/-- The integral of a globally integrable function is the unordered sum, over all
`m : ℤ`, of its integrals over the determinant slices. -/
theorem hasSum_setIntegral_determinantSlice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : LeftUnipotentQuotient n F → E} :
    letI := T.topology
    letI := borel (LeftUnipotentQuotient n F)
    Integrable f μ →
      HasSum (fun m : ℤ => ∫ q in determinantSlice T n m, f q ∂μ) (∫ q, f q ∂μ) := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F)
  let : BorelSpace (LeftUnipotentQuotient n F) := ⟨rfl⟩
  intro hf
  have h := hasSum_integral_iUnion (fun m => measurableSet_determinantSlice T n m)
    (pairwise_disjoint_determinantSlice T n)
    (by rw [iUnion_determinantSlice]; exact hf.integrableOn)
  rwa [iUnion_determinantSlice, Measure.restrict_univ] at h

/-- The norms of the slice integrals of a globally integrable function are summable. -/
theorem summable_norm_setIntegral_determinantSlice {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : LeftUnipotentQuotient n F → E} :
    letI := T.topology
    letI := borel (LeftUnipotentQuotient n F)
    Integrable f μ →
      Summable (fun m : ℤ => ‖∫ q in determinantSlice T n m, f q ∂μ‖) := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F)
  intro hf
  exact Summable.of_nonneg_of_le (fun m => norm_nonneg _)
    (fun m => norm_integral_le_integral_norm _)
    (hasSum_setIntegral_determinantSlice T μ hf.norm).summable

end Partition

/-- JPSS (4.2.2) at a convergent parameter: global integrability of the equal-rank
integrand at `s` gives slice integrability at zero, absolute summability of
`a(m) (q^(-s))^m`, and its `HasSum` to the equal-rank integral at `s`. -/
theorem equalRankSliceExpansion (F : Type uF) [Field F]
    (T : LocalFieldData F) (n : ℕ) : EqualRankSliceExpansionStatement F T n := by
  let := T.topology
  let := borel (LeftUnipotentQuotient n F)
  intro μ ψ W W' Φ s hs
  have hf : Integrable (equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ s) μ := hs
  have hslice : ∀ m : ℤ,
      ∫ q in determinantSlice T n m,
          equalRankIntegrand ψ (normalizedAbsoluteValue T) W W' Φ s q ∂μ =
        equalRankSliceCoefficient T μ ψ W W' Φ m *
          spectralPoint T.residueCardinality s ^ m :=
    fun m => setIntegral_equalRankIntegrand_determinantSlice T μ ψ W W' Φ m s
  refine ⟨fun m => (sliceIntegrableAt_equalRankIntegrand_iff T μ ψ W W' Φ m s).mp
    (sliceIntegrable_of_integrable (T := T) hf m), ?_, ?_⟩
  · simpa only [hslice] using summable_norm_setIntegral_determinantSlice T μ hf
  · have h := hasSum_setIntegral_determinantSlice T μ hf
    simp only [hslice] at h
    exact h

end Langlands.AllField.RankinSelberg
