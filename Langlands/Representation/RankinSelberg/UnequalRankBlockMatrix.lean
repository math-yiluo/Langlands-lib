import Langlands.Representation.RankinSelberg.QuotientIntegrals

/-!
# Rank-transported unequal-rank JPSS block matrices

The block matrix `unequalRankMatrix j k g Y` lives in `GL_(n + (j + k + 1) + 1)`.
Integration helpers that fix one large group `GL_(r + 1)` and vary the split
`j + k + 1 = r - n` need the same matrix with its rank written as `r + 1`.
This module transports only that natural-number rank; no block comparison,
topology, measure or analytic assertion is made here.
-/

noncomputable section

namespace Langlands.RankinSelberg.AdjacentBlockReduction

universe uF

variable {F : Type uF} [Field F]

/-- The actual block matrix with only its natural-number rank transported.
After substituting `hr : r = n + (j + k + 1)` it is exactly
`unequalRankMatrix j k g Y`. -/
def blockMatrixAt {n r : ℕ} (j k : ℕ) (hr : r = n + (j + k + 1))
    (g : Langlands.GeneralLinear (n + 1) F)
    (Y : Matrix (Fin j) (Fin (n + 1)) F) :
    Langlands.GeneralLinear (r + 1) F := by
  subst r
  exact unequalRankMatrix j k g Y

end Langlands.RankinSelberg.AdjacentBlockReduction
