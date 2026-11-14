import Langlands.Representation.RankinSelberg.CharacterChangeSingletonBlocks
import Langlands.AllField.Group.GL.BlockModulusSupplement
import Langlands.AllField.Representation.RankinSelberg.AnalyticStatementSupplement
/-!
# The character-change diagonal as a singleton Levi element

The diagonal `d_a = diag(a^n, ..., a, 1)` is the Levi element of the singleton
shape with entries `a^(n-i)`. Its conjugation of the upper unipotent group is the
Levi action on the singleton radical, and its block modulus is
`|a|^(sum_{i<j}(j-i))`.
-/

open scoped BigOperators NNReal

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement leviModulus_characterChangeLevi leviModulus_characterChangeLevi_eq_pow normalizedAbsoluteValue normalizedAbsoluteValue_apply
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.GeneralLinear.BlockShape
open Langlands.Whittaker

universe uF

section Field


end Field

section Padic

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The singleton block modulus of `characterChangeLevi a n` is
`|a|^(sum_{i<j}(j-i))`, as a unit of `ℝ≥0`. -/
theorem leviModulus_characterChangeLevi_eq_pow (a : Fˣ) (n : ℕ) :
    T.leviModulus (singletons (n + 1)) (characterChangeLevi a n) =
      T.normalizedAbsUnits a ^ characterChangeRootExponent n := by
  rw [characterChangeLevi, T.leviModulus_singletonLevi, characterChangeRootExponent,
    ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter, ← Finset.prod_pow_eq_pow_sum]
  refine Finset.prod_congr rfl fun j hj => ?_
  have hij : i < j := (Finset.mem_filter.mp hj).2
  have hn : n - i.val = (j.val - i.val) + (n - j.val) := by
    have := j.isLt
    have : i.val < j.val := hij
    omega
  rw [map_pow, map_pow, hn, pow_add, mul_div_cancel_right]

/-- The singleton block modulus of `characterChangeLevi a n` is the
character-change modulus for the normalized absolute value. -/
theorem leviModulus_characterChangeLevi (a : Fˣ) (n : ℕ) :
    ((T.leviModulus (singletons (n + 1)) (characterChangeLevi a n) : ℝ≥0)) =
      characterChangeModulus (normalizedAbsoluteValue T) a n := by
  rw [leviModulus_characterChangeLevi_eq_pow, Units.val_pow_eq_pow_val]
  apply NNReal.eq
  rw [NNReal.coe_pow, T.normalizedAbsUnits_coe]
  rfl

end Padic

end Langlands.AllField.RankinSelberg
