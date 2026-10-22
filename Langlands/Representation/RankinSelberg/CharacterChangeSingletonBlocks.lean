import Langlands.Group.GL.SingletonBlocks
import Langlands.Representation.RankinSelberg.CharacterChange
import Langlands.Representation.RankinSelberg.AnalyticStatement

/-!
# The character-change diagonal as a singleton Levi element

The diagonal `d_a = diag(a^n, ..., a, 1)` is the Levi element of the singleton
shape with entries `a^(n-i)`. Its conjugation of the upper unipotent group is the
Levi action on the singleton radical, and its block modulus is
`|a|^(sum_{i<j}(j-i))`.
-/

open scoped BigOperators NNReal

namespace Langlands.RankinSelberg

open Langlands.GeneralLinear Langlands.GeneralLinear.BlockShape Langlands.Whittaker

universe uF

section Field

variable {F : Type uF} [Field F]

/-- The character-change diagonal `diag(a^n, ..., a, 1)` as a Levi element of the
singleton shape with `n + 1` blocks. -/
def characterChangeLevi (a : Fˣ) (n : ℕ) : (singletons (n + 1)).Levi F :=
  singletonLevi F fun i : Fin (n + 1) => a ^ (n - i.val)

/-- The block diagonal matrix of `characterChangeLevi a n` is `d_a`. -/
theorem leviEmbedding_characterChangeLevi (a : Fˣ) (n : ℕ) :
    (singletons (n + 1)).leviEmbedding F (characterChangeLevi a n) =
      characterChangeElement a n := by
  apply Units.ext
  rw [characterChangeLevi, leviEmbedding_singletonLevi_val, characterChangeElement_val]

/-- Conjugation by `d_a` on the upper unipotent group is the Levi action of
`characterChangeLevi a n` on the singleton radical. -/
theorem upperUnipotentEquivRadical_characterChangeConj (a : Fˣ) (n : ℕ)
    (u : upperUnipotent (n + 1) F) :
    upperUnipotentEquivRadical F (characterChangeConj a n u) =
      (singletons (n + 1)).leviAction F (characterChangeLevi a n)
        (upperUnipotentEquivRadical F u) := by
  apply Subtype.ext
  apply Subtype.ext
  rw [leviAction_apply_val, leviEmbedding_characterChangeLevi,
    upperUnipotentEquivRadical_apply_val, upperUnipotentEquivRadical_apply_val,
    characterChangeConj_val]

end Field

section Padic

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The singleton block modulus of `characterChangeLevi a n` is
`|a|^(sum_{i<j}(j-i))`, as a unit of `ℝ≥0`. -/
theorem leviModulus_characterChangeLevi_eq_pow (a : F.Carrierˣ) (n : ℕ) :
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
theorem leviModulus_characterChangeLevi (a : F.Carrierˣ) (n : ℕ) :
    ((T.leviModulus (singletons (n + 1)) (characterChangeLevi a n) : ℝ≥0)) =
      characterChangeModulus (normalizedAbsoluteValue T) a n := by
  rw [leviModulus_characterChangeLevi_eq_pow, Units.val_pow_eq_pow_val]
  apply NNReal.eq
  rw [NNReal.coe_pow, T.normalizedAbsUnits_coe]
  rfl

end Padic

end Langlands.RankinSelberg
