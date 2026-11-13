import Langlands.Group.GL.UnramifiedCharacter
import Langlands.AllField.Group.GL.NormalizedCharacter
/-!
# All complex unramified determinant characters

The character with uniformizer value `z : ℂˣ` is `x ↦ z ^ ord(x)`.
This uses the actual normalized valuation and matrix determinant. Its kernel
is open, so the resulting character is continuous for the usual topology on `ℂ`.
-/

noncomputable section

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- The normalized additive order on nonzero field elements, in multiplicative notation. -/
def ordUnits : Fˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (T.ord (a : F))
  map_one' := congrArg Multiplicative.ofAdd T.ord_one
  map_mul' a b := congrArg Multiplicative.ofAdd (T.ord_mul a.ne_zero b.ne_zero)

@[simp]
theorem ordUnits_apply (a : Fˣ) :
    (T.ordUnits a).toAdd = T.ord (a : F) := rfl

/-- On nonzero elements, order zero is exactly normalized absolute value one. -/
theorem ord_eq_zero_iff_normalizedAbs (a : Fˣ) :
    T.ord (a : F) = 0 ↔ T.normalizedAbs a = 1 := by
  rw [T.normalizedAbs_eq_one_iff_discreteValuation]
  change -WithZero.log (T.discreteValuation (a : F)) = 0 ↔ _
  rw [neg_eq_zero]
  constructor
  · intro h
    have he := WithZero.exp_log (T.discreteValuation.ne_zero_iff.mpr a.ne_zero)
    simpa [h] using he.symm
  · intro h
    simp [h]

theorem ker_ordUnits : T.ordUnits.ker = T.normalizedAbsUnits.ker := by
  ext a
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Units.val_inj, ← NNReal.coe_inj]
  change T.ord (a : F) = 0 ↔ T.normalizedAbs a = 1
  exact T.ord_eq_zero_iff_normalizedAbs a

/-- The chosen uniformizer as a field unit, reusing the shared constructor. -/
abbrev uniformizerUnit : Fˣ :=
  Langlands.LocalFactor.LocalAbelian.uniformizerUnit T

@[simp]
theorem uniformizerUnit_val : (T.uniformizerUnit : F) = T.uniformizer := rfl

end Langlands.LocalFieldData
