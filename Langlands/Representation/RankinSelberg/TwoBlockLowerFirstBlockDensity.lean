import Langlands.Representation.RankinSelberg.DeterminantSlices

/-!
# The positive determinant density on a first-block slice

The residue-cardinality coefficient in JPSS Section 4.9(8) is the positive
power of the determinant absolute value on every small determinant slice.
-/

noncomputable section

namespace Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient

open GeneralLinear
open scoped ENNReal

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance lowerFirstBlockDensityTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

/-- Positivity, finiteness, and the positive determinant-power formula for the
density on a small determinant slice. -/
abbrev FirstBlockDensityStatement (n b : ℕ) (k : ℤ) : Prop :=
  let T := F.canonicalTopologicalData
  let d : ℝ≥0∞ := ENNReal.ofReal ((T.residueCardinality : ℝ) ^ (-(k * (b : ℤ))))
  0 < d ∧ d < ⊤ ∧
    ∀ v : GeneralLinear (n + 1) F.Carrier,
      (Quotient.mk _ v : LeftUnipotentQuotient n F.Carrier) ∈
        RankinSelberg.determinantSlice T n k →
      d = (ENNReal.ofReal (T.normalizedAbs
        (GeneralLinear.determinant v : F.Carrier))) ^ b

/-- On the slice of determinant order `k`, the density is
`q ^ (-(k * b)) = |det v| ^ b`, with a positive, finite value. -/
theorem firstBlockDensity (n b : ℕ) (k : ℤ) :
    FirstBlockDensityStatement F n b k := by
  let T := F.canonicalTopologicalData
  have hq : (0 : ℝ) < T.residueCardinality := by
    exact_mod_cast (zero_lt_one.trans T.residueCardinality_gt_one)
  refine ⟨ENNReal.ofReal_pos.mpr (zpow_pos hq _), ENNReal.ofReal_lt_top, ?_⟩
  intro v hv
  have hdet := (RankinSelberg.mk_mem_determinantSlice_iff_normalizedAbs T).mp hv
  change ENNReal.ofReal ((T.residueCardinality : ℝ) ^ (-(k * (b : ℤ)))) = _
  rw [hdet, ← ENNReal.ofReal_pow (zpow_pos hq (-k)).le]
  congr 1
  rw [← neg_mul, zpow_mul, zpow_natCast]

end Langlands.RankinSelberg.TwoBlockLowerFirstBlockQuotient
