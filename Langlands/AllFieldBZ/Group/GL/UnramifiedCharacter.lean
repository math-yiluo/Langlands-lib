import Langlands.AllFieldBZ.Group.GL.NormalizedCharacter
import Langlands.AllFieldBZ.LocalField.Definitions
import Langlands.Group.GL.UnramifiedCharacter

/-!
# All-field port of `Langlands.Group.GL.UnramifiedCharacter`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.UnramifiedCharacter` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe uF

variable {F : LocalFieldPackage.{uF}} (T : F.TopologicalData)

/-- The normalized additive order on nonzero field elements, in multiplicative notation. -/
def ordUnits : F.Carrierˣ →* Multiplicative ℤ where
  toFun a := Multiplicative.ofAdd (T.ord (a : F.Carrier))
  map_one' := congrArg Multiplicative.ofAdd T.ord_one
  map_mul' a b := congrArg Multiplicative.ofAdd (T.ord_mul a.ne_zero b.ne_zero)

@[simp]
theorem ordUnits_apply (a : F.Carrierˣ) :
    (T.ordUnits a).toAdd = T.ord (a : F.Carrier) := rfl

/-- On nonzero elements, order zero is exactly normalized absolute value one. -/
theorem ord_eq_zero_iff_normalizedAbs (a : F.Carrierˣ) :
    T.ord (a : F.Carrier) = 0 ↔ T.normalizedAbs a = 1 := by
  rw [T.normalizedAbs_eq_one_iff_discreteValuation]
  change -WithZero.log (T.discreteValuation (a : F.Carrier)) = 0 ↔ _
  rw [neg_eq_zero]
  constructor
  · intro h
    have he := WithZero.exp_log (T.discreteValuation.ne_zero_iff.mpr a.ne_zero)
    simpa [h] using he.symm
  · intro h
    simp [h]

/-- All complex values are allowed; there is no real-power or unitary restriction. -/
def unramifiedCharacter (z : ℂˣ) : F.Carrierˣ →* ℂˣ :=
  (zpowersHom ℂˣ z).comp T.ordUnits

@[simp]
theorem unramifiedCharacter_apply (z : ℂˣ) (a : F.Carrierˣ) :
    T.unramifiedCharacter z a = z ^ T.ord (a : F.Carrier) := rfl

/-- Dependence on the uniformizer value is a group homomorphism. -/
def unramifiedCharacterHom : ℂˣ →* (F.Carrierˣ →* ℂˣ) where
  toFun := T.unramifiedCharacter
  map_one' := by ext a; simp
  map_mul' z w := by ext a; simp [mul_zpow]

@[simp]
theorem unramifiedCharacter_one : T.unramifiedCharacter 1 = 1 :=
  T.unramifiedCharacterHom.map_one

@[simp]
theorem unramifiedCharacter_mul (z w : ℂˣ) :
    T.unramifiedCharacter (z * w) = T.unramifiedCharacter z * T.unramifiedCharacter w :=
  T.unramifiedCharacterHom.map_mul z w

@[simp]
theorem unramifiedCharacter_inv (z : ℂˣ) :
    T.unramifiedCharacter z⁻¹ = (T.unramifiedCharacter z)⁻¹ :=
  map_inv T.unramifiedCharacterHom z

/-- The chosen uniformizer as a field unit, reusing the shared constructor. -/
abbrev uniformizerUnit : F.Carrierˣ :=
  Langlands.LocalFactor.LocalAbelian.uniformizerUnit T

@[simp]
theorem uniformizerUnit_val : (T.uniformizerUnit : F.Carrier) = T.uniformizer := rfl

@[simp]
theorem unramifiedCharacter_uniformizer (z : ℂˣ) :
    T.unramifiedCharacter z T.uniformizerUnit = z := by
  simp [T.ord_uniformizer]

/-- The actual determinant pullback of the unramified field character. -/
def determinantUnramifiedCharacter (n : ℕ) (z : ℂˣ) :
    GeneralLinear n F.Carrier →* ℂˣ :=
  (T.unramifiedCharacter z).comp GeneralLinear.determinant

@[simp]
theorem determinantUnramifiedCharacter_apply (n : ℕ) (z : ℂˣ)
    (g : GeneralLinear n F.Carrier) :
    T.determinantUnramifiedCharacter n z g =
      z ^ T.ord (GeneralLinear.determinant g : F.Carrier) := rfl

@[simp]
theorem determinantUnramifiedCharacter_one (n : ℕ) :
    T.determinantUnramifiedCharacter n 1 = 1 := by
  ext g
  simp

@[simp]
theorem determinantUnramifiedCharacter_mul (n : ℕ) (z w : ℂˣ) :
    T.determinantUnramifiedCharacter n (z * w) =
      T.determinantUnramifiedCharacter n z * T.determinantUnramifiedCharacter n w := by
  ext g
  simp [mul_zpow]

@[simp]
theorem determinantUnramifiedCharacter_inv (n : ℕ) (z : ℂˣ) :
    T.determinantUnramifiedCharacter n z⁻¹ = (T.determinantUnramifiedCharacter n z)⁻¹ := by
  ext g
  simp

@[simp]
theorem determinantUnramifiedCharacter_scalar (n : ℕ) (z : ℂˣ) (a : F.Carrierˣ) :
    T.determinantUnramifiedCharacter n z (GeneralLinear.scalar a) =
      T.unramifiedCharacter z a ^ n := by
  change T.unramifiedCharacter z (Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.scalar (Fin n) a)) = _
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow]

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
