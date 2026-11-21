import Langlands.Global.RankinSelberg.RealLocalNormalizedGrowth
import Langlands.Global.RankinSelberg.RealLocalEqualRankZeroGrowth

/-! # Rank-indexed normalized-growth statements for the real induction -/

noncomputable section

open Langlands.LocalFactor.Archimedean
open scoped NNReal

set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.RealJacquet

open ArchimedeanLocal

/-- Equal-rank normalized growth at one rank, on the uniform coefficient spaces, with the
dual lists, epsilon parameter `-a`, scale `sqrt |a|` and sign `det(ds, -1) ^ r` of
`RealLocalUniformPositiveEqualContinuationStatement`. -/
def RealLocalEqualGrowthAtRank (r : ℕ) : Prop :=
  ∀ (ds es : List RealBlock), realRank ds = r + 1 → realRank es = r + 1 →
  ∀ (a : ℝˣ) (D : RealQuotientMeasureData r) (W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (Φ : SchwartzMap (Fin (r + 1) → ℝ) ℂ),
    W ∈ realUniformWhittakerModel r ds a → W' ∈ realUniformWhittakerModel r es (-a) →
    HasRealPairNormalizedGrowth ds es (ds.map RealLocalJacquet.dualBlock)
      (es.map RealLocalJacquet.dualBlock) (-a) (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
      ((RealJacquet.determinant ds (-1) : ℂ) ^ r)
      (realEqualIntegral D W W' Φ) (realEqualDualIntegral (-a) D W W' Φ)

/-- Unequal-rank normalized growth at two ranks `t < r`, on the uniform coefficient spaces,
with the dual lists, epsilon parameter `-a`, scale `sqrt |a|` and sign
`det(ds, -1) ^ (t + 1) * det(es, -1)` of `RealLocalUniformUnequalContinuationStatement`. -/
def RealLocalUnequalGrowthAtRanks (r t : ℕ) (h : t < r) : Prop :=
  ∀ (ds es : List RealBlock), realRank ds = r + 1 → realRank es = t + 1 →
  ∀ (a : ℝˣ) (D : RealQuotientMeasureData t) (W : Langlands.GeneralLinear (r + 1) ℝ → ℂ)
    (W' : Langlands.GeneralLinear (t + 1) ℝ → ℂ),
    W ∈ realUniformWhittakerModel r ds a → W' ∈ realUniformWhittakerModel t es (-a) →
    HasRealPairNormalizedGrowth ds es (ds.map RealLocalJacquet.dualBlock)
      (es.map RealLocalJacquet.dualBlock) (-a) (NNReal.sqrt ‖(a : ℝ)‖₊)
      (NNReal.sqrt_pos.mpr (nnnorm_pos.mpr a.ne_zero))
      ((RealJacquet.determinant ds (-1) : ℂ) ^ (t + 1) * (RealJacquet.determinant es (-1) : ℂ))
      (realUnequalIntegral h D W W') (realUnequalDualIntegral h a D W W')

/-- Adjacent-rank normalized growth: the unequal statement at ranks `r + 1` and `r`. -/
def RealLocalAdjacentGrowthAtRank (r : ℕ) : Prop :=
  RealLocalUnequalGrowthAtRanks (r + 1) r (Nat.lt_succ_self r)

/-- Rank zero of the equal-rank statement is the staged rank-zero theorem. -/
theorem realLocalEqualGrowthAtRank_zero : RealLocalEqualGrowthAtRank 0 :=
  realLocalEqualRankZeroGrowth

/-- Unequal growth at all pairs of ranks gives the exact unequal continuation target. -/
theorem realLocalUniformUnequalContinuation_of_growth
    (hG : ∀ (r t : ℕ) (h : t < r), RealLocalUnequalGrowthAtRanks r t h) :
    RealLocalUniformUnequalContinuationStatement := by
  intro r t h ds es hds hes a D W W' hW hW'
  exact (hG r t h ds es hds hes a D W W' hW hW').unequalContinuation

/-- Equal growth at all positive ranks gives the exact positive equal continuation target. -/
theorem realLocalUniformPositiveEqualContinuation_of_growth
    (hG : ∀ r : ℕ, 0 < r → RealLocalEqualGrowthAtRank r) :
    RealLocalUniformPositiveEqualContinuationStatement := by
  intro r hr ds es hds hes a D W W' Φ hW hW'
  exact (hG r hr ds es hds hes a D W W' Φ hW hW').equalContinuation

end Langlands.Global.RankinSelbergGlobal.RealJacquet
