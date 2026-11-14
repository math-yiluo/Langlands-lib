import Langlands.Representation.RankinSelberg.IntegralDeterminant
import Langlands.AllField.Group.GL.PadicSupplement
/-! # Normalized determinant of an integral invertible matrix -/

noncomputable section

namespace Langlands.AllField.RankinSelberg
open Langlands.RankinSelberg hiding normalizedAbs_det_of_mem_integralSubgroup
open Langlands.AllField.RankinSelberg

universe uF

variable {F : Type uF} [Field F] (T : LocalFieldData F)

/-- An integral invertible matrix has determinant of normalized absolute value one. -/
theorem normalizedAbs_det_of_mem_integralSubgroup {r : ℕ}
    {k : Langlands.GeneralLinear (r + 1) F}
    (hk : k ∈ Conductor.integralSubgroup T.Integers r) :
    T.normalizedAbs (Matrix.det k.val) = 1 := by
  have hmem := (Conductor.mem_integralSubgroup _ _ k).mp hk
  have h1 : Matrix.det k.val ∈ T.Integers :=
    GeneralLinear.Cartan.det_mem_integer _ hmem.1
  have h2 : Matrix.det (k⁻¹).val ∈ T.Integers :=
    GeneralLinear.Cartan.det_mem_integer _ hmem.2
  have hprod : Matrix.det k.val * Matrix.det (k⁻¹).val = 1 := by
    rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.det_one]
  have ha := (T.normalizedAbs_le_one_iff_mem_integers _).mpr h1
  have hb := (T.normalizedAbs_le_one_iff_mem_integers _).mpr h2
  have hab : T.normalizedAbs (Matrix.det k.val) * T.normalizedAbs (Matrix.det (k⁻¹).val) = 1 := by
    rw [← T.normalizedAbs_mul, hprod, T.normalizedAbs_one]
  nlinarith [T.normalizedAbs_nonneg (Matrix.det k.val),
    T.normalizedAbs_nonneg (Matrix.det (k⁻¹).val)]

end Langlands.AllField.RankinSelberg
