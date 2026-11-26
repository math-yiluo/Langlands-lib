import Langlands.Global.RankinSelberg.RealGapCanonicalGrowth
import Langlands.Global.RankinSelberg.RealLocalPositiveEqualReduction
import Langlands.Global.RankinSelberg.RealUniformTailInclusion

/-! # The real unequal-rank continuation and local functional equation -/

noncomputable section

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open RealGapRankCoordinates (rankLT)

/-- Adjacent-rank character growth at every rank. -/
theorem realLocalAdjacentCharacterGrowth (r : ℕ) : RealLocalAdjacentCharacterGrowthAtRank r :=
  realAdjacentFromEqualGrowth (r := r) RealUniformCanonicalRange.realUniformCanonicalRangePremise
    (realOrthogonalCompactProjectionPremise r)
    (realLocalEqualCharacterGrowth_of_canonicalPremises
      RealUniformCanonicalRange.realUniformCanonicalRangePremise
      RealUniformCanonicalRange.realCanonicalStandardEvaluationPremise r)

private theorem gapGrowth_all (t : ℕ) :
    ∀ q : ℕ, RealLocalUnequalCharacterGrowthAtRanks (t + 1 + q) t (rankLT t q) := by
  intro q
  induction q with
  | zero => exact realLocalAdjacentCharacterGrowth t
  | succ q ih => exact RealGapCanonicalGrowth.realGapGrowthStep t q ih

/-- Character-list growth for ranks with a gap of at least two. -/
theorem realLocalUnequalCharacterGrowth_gap :
    ∀ (r t : ℕ) (h : t < r), t + 1 < r → RealLocalUnequalCharacterGrowthAtRanks r t h := by
  intro r t h hgap
  obtain ⟨q, rfl⟩ : ∃ q, r = t + 1 + q := ⟨r - (t + 1), by omega⟩
  exact gapGrowth_all t q

/-- Character-list growth at every pair of ranks. -/
theorem realLocalUnequalCharacterGrowth :
    ∀ (r t : ℕ) (h : t < r), RealLocalUnequalCharacterGrowthAtRanks r t h := by
  intro r t h
  obtain ⟨q, rfl⟩ : ∃ q, r = t + 1 + q := ⟨r - (t + 1), by omega⟩
  exact gapGrowth_all t q

end Langlands.Global.RankinSelbergGlobal.RealJacquet

namespace Langlands.Global.RankinSelbergGlobal

/-- The real unequal-rank continuation and local functional equation on the uniform coefficient
spaces. -/
theorem realLocalUniformUnequalContinuation : RealLocalUniformUnequalContinuationStatement :=
  RealJacquet.realLocalUniformUnequalContinuation_of_unequalCharacterGrowth
    RealJacquet.realLocalUnequalCharacterGrowth

end Langlands.Global.RankinSelbergGlobal
