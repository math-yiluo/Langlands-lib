import Langlands.Group.GL.LowerBlockQuotientCoordinates
import Langlands.Representation.RankinSelberg.WhittakerNormData
import Mathlib.Topology.Algebra.GroupWithZero

/-! # Actual quotient chart and determinant density for the intermediate tail -/

noncomputable section

namespace Langlands.RankinSelberg.InducedTailIntermediate

open GeneralLinear QuotientIntegration MeasureTheory
open scoped ENNReal

universe uF

variable {F : Type uF} [Field F]

section Chart

variable [TopologicalSpace F]

/-- The published lower-block chart, with its target rank expressed in the
indexing convention of the actual JPSS quotient. -/
def quotientChart (n d : ℕ)
    (z : LeftUnipotentQuotient n F ×
      (Matrix (Fin d) (Fin (n + 1)) F × lowerTriangularSubgroup d F)) :
    LeftUnipotentQuotient (n + d) F :=
  upperUnipotentQuotientCongr (by omega : (n + 1) + d = (n + d) + 1)
    (lowerBlockQuotientChart z)

/-- Its evaluation at an actual representative uses only numerical rank
reindexing of the actual lower-block matrix. -/
@[simp] theorem quotientChart_mk (n d : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F)
    (x : Matrix (Fin d) (Fin (n + 1)) F) (h : lowerTriangularSubgroup d F) :
    quotientChart n d (Quotient.mk _ g, x, h) =
      Quotient.mk _
        (reindex (finCongr (by omega : (n + 1) + d = n + d + 1))
          (lowerBlockPair g x h)) :=
  rfl

theorem quotientChart_injective (n d : ℕ) :
    Function.Injective (quotientChart (F := F) n d) :=
  (upperUnipotentQuotientCongr (R := F)
    (by omega : (n + 1) + d = n + d + 1)).injective.comp
      lowerBlockQuotientChart_injective

end Chart

/-- The positive finite density on the small quotient. It is a function on
cosets, rather than a choice of a representative's determinant. -/
def quotientDensity (abv : AbsoluteValue F ℝ) (n d : ℕ)
    (q : LeftUnipotentQuotient n F) : ℝ≥0∞ :=
  ENNReal.ofReal (quotientDeterminantAbs abv n q ^ (-(d : ℤ)))

@[simp] theorem quotientDensity_mk (abv : AbsoluteValue F ℝ) (n d : ℕ)
    (g : Langlands.GeneralLinear (n + 1) F) :
    quotientDensity abv n d (Quotient.mk _ g) =
      ENNReal.ofReal (abv (Matrix.det g.val) ^ (-(d : ℤ))) :=
  rfl

theorem quotientDensity_ne_top (abv : AbsoluteValue F ℝ) (n d : ℕ)
    (q : LeftUnipotentQuotient n F) : quotientDensity abv n d q ≠ ∞ :=
  ENNReal.ofReal_ne_top

theorem quotientDensity_pos (abv : AbsoluteValue F ℝ) (n d : ℕ)
    (q : LeftUnipotentQuotient n F) : 0 < quotientDensity abv n d q :=
  ENNReal.ofReal_pos.mpr (zpow_pos (quotientDeterminantAbs_pos abv n q) _)

theorem quotientDensity_toReal (abv : AbsoluteValue F ℝ) (n d : ℕ)
    (q : LeftUnipotentQuotient n F) :
    (quotientDensity abv n d q).toReal =
      quotientDeterminantAbs abv n q ^ (-(d : ℤ)) :=
  ENNReal.toReal_ofReal (zpow_nonneg (quotientDeterminantAbs_nonneg abv n q) _)

/-- This is also the power-of-`ofReal` form used in measure disintegration. -/
theorem quotientDensity_eq_ofReal_zpow (abv : AbsoluteValue F ℝ) (n d : ℕ)
    (q : LeftUnipotentQuotient n F) :
    quotientDensity abv n d q =
      ENNReal.ofReal (quotientDeterminantAbs abv n q) ^ (-(d : ℤ)) := by
  unfold quotientDensity
  rw [zpow_neg, zpow_natCast, ENNReal.zpow_neg, zpow_natCast,
    ENNReal.ofReal_inv_of_pos (pow_pos (quotientDeterminantAbs_pos abv n q) d),
    ENNReal.ofReal_pow (quotientDeterminantAbs_nonneg abv n q)]

section Topology

variable [TopologicalSpace F] [IsTopologicalRing F]

theorem continuous_quotientChart (n d : ℕ) :
    Continuous (quotientChart (F := F) n d) :=
  (upperUnipotentQuotientCongr (R := F)
    (by omega : (n + 1) + d = n + d + 1)).continuous.comp
      continuous_lowerBlockQuotientChart

/-- Continuity of the determinant norm descends through the open quotient map. -/
theorem continuous_quotientDeterminantAbs (abv : AbsoluteValue F ℝ)
    (habv : Continuous abv) (n : ℕ) :
    Continuous (quotientDeterminantAbs abv n) := by
  apply (leftQuotient_isOpenQuotientMap
    (upperUnipotent (n + 1) F)).isQuotientMap.continuous_iff.mpr
  exact habv.comp Units.continuous_val.matrix_det

theorem continuous_quotientDensity (abv : AbsoluteValue F ℝ)
    (habv : Continuous abv) (n d : ℕ) :
    Continuous (quotientDensity abv n d) :=
  ENNReal.continuous_ofReal.comp
    ((continuous_quotientDeterminantAbs abv habv n).zpow₀ (-(d : ℤ))
      (fun q => Or.inl (ne_of_gt (quotientDeterminantAbs_pos abv n q))))

theorem measurable_quotientDensity (abv : AbsoluteValue F ℝ)
    (habv : Continuous abv) (n d : ℕ)
    [MeasurableSpace (LeftUnipotentQuotient n F)]
    [BorelSpace (LeftUnipotentQuotient n F)] :
    Measurable (quotientDensity abv n d) :=
  (continuous_quotientDensity abv habv n d).measurable

end Topology

end Langlands.RankinSelberg.InducedTailIntermediate
