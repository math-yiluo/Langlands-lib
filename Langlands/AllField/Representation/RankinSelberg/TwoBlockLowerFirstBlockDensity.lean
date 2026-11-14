import Langlands.Representation.RankinSelberg.TwoBlockLowerFirstBlockDensity
import Langlands.AllField.Representation.RankinSelberg.DeterminantSlicesSupplement
/-!
# The positive determinant density on a first-block slice

The residue-cardinality coefficient in JPSS Section 4.9(8) is the positive
power of the determinant absolute value on every small determinant slice.
-/

noncomputable section

namespace Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient hiding FirstBlockDensityStatement firstBlockDensity
open Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement SliceIntegrable SliceIntegrableAt UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement continuous_determinantOrder continuous_ord_units determinantOrder determinantOrder_mk determinantOrder_rightTranslate determinantSlice disjoint_determinantSlice equalRankIntegrand_eq_mul_spectralPoint_zpow equalRankSliceCoefficient equalRankSliceCoefficient_def iUnion_determinantSlice isClopen_determinantSlice isClosed_determinantSlice isEqualRankLPolynomial_characterChange_normalized isOpen_determinantSlice measurableSet_determinantSlice mem_determinantSlice mk_mem_determinantSlice mk_mem_determinantSlice_iff_normalizedAbs normalizedAbsoluteValue normalizedAbsoluteValue_apply normalizedDeterminantWeight_eq_spectralPoint_zpow pairwise_disjoint_determinantSlice rightTranslate_mem_determinantSlice setIntegral_equalRankIntegrand_determinantSlice sliceCoefficient sliceCoefficient_eq_integral_indicator sliceCoefficient_smul sliceIntegrableAt_equalRankIntegrand_iff sliceIntegrableAt_iff sliceIntegrable_of_integrable zetaSpan_equalRank_characterChange_normalized
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open scoped ENNReal

universe uF

variable (F : Type uF) [Field F]

/-- Positivity, finiteness, and the positive determinant-power formula for the
density on a small determinant slice. -/
abbrev FirstBlockDensityStatement [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (n b : ℕ) (k : ℤ) : Prop :=
  let T := (⟨⟩ : LocalFieldData F)
  let d : ℝ≥0∞ := ENNReal.ofReal ((T.residueCardinality : ℝ) ^ (-(k * (b : ℤ))))
  0 < d ∧ d < ⊤ ∧
    ∀ v : GeneralLinear (n + 1) F,
      (Quotient.mk _ v : LeftUnipotentQuotient n F) ∈
        Langlands.AllField.RankinSelberg.determinantSlice T n k →
      d = (ENNReal.ofReal (T.normalizedAbs
        (GeneralLinear.determinant v : F))) ^ b

/-- On the slice of determinant order `k`, the density is
`q ^ (-(k * b)) = |det v| ^ b`, with a positive, finite value. -/
theorem firstBlockDensity [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F] (n b : ℕ) (k : ℤ) :
    FirstBlockDensityStatement F n b k := by
  let T := (⟨⟩ : LocalFieldData F)
  have hq : (0 : ℝ) < T.residueCardinality := by
    exact_mod_cast (zero_lt_one.trans T.residueCardinality_gt_one)
  refine ⟨ENNReal.ofReal_pos.mpr (zpow_pos hq _), ENNReal.ofReal_lt_top, ?_⟩
  intro v hv
  have hdet := (Langlands.AllField.RankinSelberg.mk_mem_determinantSlice_iff_normalizedAbs T).mp hv
  change ENNReal.ofReal ((T.residueCardinality : ℝ) ^ (-(k * (b : ℤ)))) = _
  rw [hdet, ← ENNReal.ofReal_pow (zpow_pos hq (-k)).le]
  congr 1
  rw [← neg_mul, zpow_mul, zpow_natCast]

end Langlands.AllField.RankinSelberg.TwoBlockLowerFirstBlockQuotient
