import Langlands.LocalField.Normalization.ComplexCharacter
import Langlands.Group.GL.UnramifiedCharacter
import Langlands.LocalFactor.Euler.Definitions

/-! # Continuous complex powers of the normalized absolute value -/

noncomputable section

universe uF

namespace Langlands.PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The existing continuous unramified character at the spectral value `q^(-s)`. -/
def normalizedAbsPowerCharacter (s : ℂ) :
    letI := T.topology
    F.Carrierˣ →ₜ* ℂˣ :=
  T.unramifiedCharacterContinuous
    (LocalFactor.spectralParameter T.residueCardinality
      (by exact_mod_cast (zero_lt_one.trans T.residueCardinality_gt_one)) s)

/-- Its value is the actual normalized absolute value raised to the complex
power, expressed by the real logarithm of a strictly positive real number. -/
theorem normalizedAbsPowerCharacter_apply (s : ℂ) (a : F.Carrierˣ) :
    (T.normalizedAbsPowerCharacter s a : ℂ) =
      Complex.exp (s * (Real.log (T.normalizedAbs (a : F.Carrier)) : ℂ)) := by
  change (((LocalFactor.spectralParameter T.residueCardinality
      (by exact_mod_cast (zero_lt_one.trans T.residueCardinality_gt_one)) s) ^
      T.ord (a : F.Carrier) : ℂˣ) : ℂ) = _
  rw [Units.val_zpow_eq_zpow_val]
  change Complex.exp (-s * (Real.log (T.residueCardinality : ℝ) : ℂ)) ^
    T.ord (a : F.Carrier) = _
  rw [T.normalizedAbs_of_ne_zero a.ne_zero, Real.log_zpow, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

@[simp]
theorem normalizedAbsPowerCharacter_zero : T.normalizedAbsPowerCharacter 0 = 1 := by
  let := T.topology
  apply ContinuousMonoidHom.ext
  intro a
  apply Units.ext
  simp [normalizedAbsPowerCharacter_apply]

theorem normalizedAbsPowerCharacter_add (s t : ℂ) :
    T.normalizedAbsPowerCharacter (s + t) =
      T.normalizedAbsPowerCharacter s * T.normalizedAbsPowerCharacter t := by
  let := T.topology
  apply ContinuousMonoidHom.ext
  intro a
  apply Units.ext
  simp only [ContinuousMonoidHom.mul_apply, Units.val_mul,
    normalizedAbsPowerCharacter_apply, add_mul, Complex.exp_add]

@[simp]
theorem normalizedAbsPowerCharacter_one :
    T.normalizedAbsPowerCharacter 1 = T.normalizedAbsCharacter := by
  let := T.topology
  apply ContinuousMonoidHom.ext
  intro a
  apply Units.ext
  rw [normalizedAbsPowerCharacter_apply]
  simp only [one_mul, normalizedAbsCharacter_apply]
  rw [← Complex.ofReal_exp, Real.exp_log (T.normalizedAbs_pos a.ne_zero)]

end Langlands.PadicField.TopologicalData
