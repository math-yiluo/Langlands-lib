import Langlands.Group.GL.NormalizedCharacter
import Langlands.LocalField.Uniformizer
import Langlands.Representation.Twist.RealPower
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Group.Hom.Instances
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Algebra.Group.Neighborhood

/-!
# All complex unramified determinant characters

The character with uniformizer value `z : ℂˣ` is `x ↦ z ^ ord(x)`.
This uses the actual normalized valuation and matrix determinant. Its kernel
is open, so the resulting character is continuous for the usual topology on `ℂ`.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

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

theorem ker_ordUnits : T.ordUnits.ker = T.normalizedAbsUnits.ker := by
  ext a
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Units.val_inj, ← NNReal.coe_inj]
  change T.ord (a : F.Carrier) = 0 ↔ T.normalizedAbs a = 1
  exact T.ord_eq_zero_iff_normalizedAbs a

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

theorem ker_ordUnits_le_ker_unramifiedCharacter (z : ℂˣ) :
    T.ordUnits.ker ≤ (T.unramifiedCharacter z).ker := by
  intro a ha
  change T.ordUnits a = 1 at ha
  change (zpowersHom ℂˣ z) (T.ordUnits a) = 1
  rw [ha, map_one]

theorem isOpen_ker_unramifiedCharacter (z : ℂˣ) :
    letI := T.topology
    IsOpen ((T.unramifiedCharacter z).ker : Set F.Carrierˣ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply Subgroup.isOpen_mono (T.ker_ordUnits_le_ker_unramifiedCharacter z)
  rw [T.ker_ordUnits]
  exact T.isOpen_ker_normalizedAbsUnits

theorem continuous_unramifiedCharacter (z : ℂˣ) :
    letI := T.topology
    Continuous (T.unramifiedCharacter z) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  apply continuous_of_tendsto_nhds_one (T.unramifiedCharacter z)
  apply Filter.Tendsto.congr' _ tendsto_const_nhds
  filter_upwards [(T.isOpen_ker_unramifiedCharacter z).mem_nhds
    (T.unramifiedCharacter z).ker.one_mem] with a ha
  exact (MonoidHom.mem_ker.mp ha).symm

/-- The same character with its proved continuity bundled. -/
def unramifiedCharacterContinuous (z : ℂˣ) :
    letI := T.topology
    F.Carrierˣ →ₜ* ℂˣ := by
  letI := T.topology
  exact { toMonoidHom := T.unramifiedCharacter z
          continuous_toFun := T.continuous_unramifiedCharacter z }

/-- The chosen uniformizer as a field unit, reusing the shared constructor. -/
abbrev uniformizerUnit : F.Carrierˣ :=
  Langlands.LocalFactor.PadicAbelian.uniformizerUnit T

@[simp]
theorem uniformizerUnit_val : (T.uniformizerUnit : F.Carrier) = T.uniformizer := rfl

@[simp]
theorem unramifiedCharacter_uniformizer (z : ℂˣ) :
    T.unramifiedCharacter z T.uniformizerUnit = z := by
  simp [T.ord_uniformizer]

/-- The parameter is recovered by evaluation at a uniformizer. -/
theorem unramifiedCharacter_injective : Function.Injective T.unramifiedCharacter := by
  intro z w h
  simpa only [unramifiedCharacter_uniformizer] using
    congrArg (fun χ : F.Carrierˣ →* ℂˣ => χ T.uniformizerUnit) h

/-- Triviality on the actual valuation-unit subgroup, without assuming continuity. -/
def IsUnramifiedCharacter (χ : F.Carrierˣ →* ℂˣ) : Prop :=
  T.normalizedAbsUnits.ker ≤ χ.ker

theorem isUnramifiedCharacter (z : ℂˣ) : T.IsUnramifiedCharacter (T.unramifiedCharacter z) := by
  rw [IsUnramifiedCharacter, ← T.ker_ordUnits]
  exact T.ker_ordUnits_le_ker_unramifiedCharacter z

/-- Every character trivial on valuation units is one of the constructed characters. -/
theorem eq_unramifiedCharacter (χ : F.Carrierˣ →* ℂˣ)
    (hχ : T.IsUnramifiedCharacter χ) :
    χ = T.unramifiedCharacter (χ T.uniformizerUnit) := by
  apply MonoidHom.ext
  intro a
  have hk : a * T.uniformizerUnit ^ (-T.ord (a : F.Carrier)) ∈ T.ordUnits.ker := by
    change T.ord ((a * T.uniformizerUnit ^ (-T.ord (a : F.Carrier)) : F.Carrierˣ) : F.Carrier) = 0
    rw [Units.val_mul, T.ord_mul a.ne_zero (Units.ne_zero _)]
    simp only [Units.val_zpow_eq_zpow_val, uniformizerUnit_val, T.ord_zpow,
      T.ord_uniformizer, mul_one, add_neg_cancel]
  rw [T.ker_ordUnits] at hk
  have he := hχ hk
  change χ (a * T.uniformizerUnit ^ (-T.ord (a : F.Carrier))) = 1 at he
  simpa only [unramifiedCharacter_apply, map_mul, map_zpow, zpow_neg, map_inv,
    mul_inv_eq_one] using he

/-- All unramified field characters, parametrized by an arbitrary nonzero complex value. -/
def unramifiedCharacterEquiv : ℂˣ ≃ {χ : F.Carrierˣ →* ℂˣ // T.IsUnramifiedCharacter χ} where
  toFun z := ⟨T.unramifiedCharacter z, T.isUnramifiedCharacter z⟩
  invFun χ := χ.val T.uniformizerUnit
  left_inv := T.unramifiedCharacter_uniformizer
  right_inv χ := Subtype.ext (T.eq_unramifiedCharacter χ.val χ.property).symm

/-- Unramifiedness already implies continuity for the usual complex topology. -/
theorem continuous_of_isUnramifiedCharacter (χ : F.Carrierˣ →* ℂˣ)
    (hχ : T.IsUnramifiedCharacter χ) :
    letI := T.topology
    Continuous χ := by
  rw [T.eq_unramifiedCharacter χ hχ]
  exact T.continuous_unramifiedCharacter _

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

theorem isOpen_ker_determinantUnramifiedCharacter (n : ℕ) (z : ℂˣ) :
    letI := T.topology
    IsOpen ((T.determinantUnramifiedCharacter n z).ker : Set (GeneralLinear n F.Carrier)) := by
  let := T.topology
  change IsOpen (GeneralLinear.determinant ⁻¹'
    ((T.unramifiedCharacter z).ker : Set F.Carrierˣ))
  exact (T.isOpen_ker_unramifiedCharacter z).preimage (T.generalLinearDeterminant n).continuous

theorem ker_determinant_le_ker_determinantUnramifiedCharacter (n : ℕ) (z : ℂˣ) :
    (GeneralLinear.determinant : GeneralLinear n F.Carrier →* F.Carrierˣ).ker ≤
      (T.determinantUnramifiedCharacter n z).ker := by
  intro g hg
  change GeneralLinear.determinant g = 1 at hg
  change T.unramifiedCharacter z (GeneralLinear.determinant g) = 1
  rw [hg, map_one]

/-- Every determinant of normalized absolute value one is in the character kernel. -/
theorem ker_determinantNorm_le_ker_determinantUnramifiedCharacter (n : ℕ) (z : ℂˣ) :
    (T.determinantNorm n).ker ≤ (T.determinantUnramifiedCharacter n z).ker := by
  intro g hg
  exact T.isUnramifiedCharacter z hg

@[simp]
theorem determinantUnramifiedCharacter_scalar (n : ℕ) (z : ℂˣ) (a : F.Carrierˣ) :
    T.determinantUnramifiedCharacter n z (GeneralLinear.scalar a) =
      T.unramifiedCharacter z a ^ n := by
  change T.unramifiedCharacter z (Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.scalar (Fin n) a)) = _
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow]

/-- The normalized real-power character is contained in the full complex family. -/
theorem realPowerCharacter_eq_unramifiedCharacter (s : ℝ) :
    Langlands.realPowerCharacter T.normalizedAbsUnits s =
      T.unramifiedCharacter
        (Langlands.realPowerCharacter T.normalizedAbsUnits s T.uniformizerUnit) :=
  T.eq_unramifiedCharacter _ (Langlands.ker_le_realPowerCharacter_ker _ s)

/-- Pullback identifies the already constructed normalized determinant real powers. -/
theorem realPowerDeterminant_eq_unramifiedCharacter (n : ℕ) (s : ℝ) :
    Langlands.realPowerCharacter (T.determinantNorm n) s =
      T.determinantUnramifiedCharacter n
        (Langlands.realPowerCharacter T.normalizedAbsUnits s T.uniformizerUnit) := by
  change (Langlands.realPowerCharacter T.normalizedAbsUnits s).comp
    GeneralLinear.determinant = _
  exact congrArg (fun χ : F.Carrierˣ →* ℂˣ => χ.comp GeneralLinear.determinant)
    (T.realPowerCharacter_eq_unramifiedCharacter s)

/-- The determinant pullback with its actual matrix topology and proved continuity. -/
def determinantUnramifiedCharacterContinuous (n : ℕ) (z : ℂˣ) :
    letI := T.topology
    GeneralLinear n F.Carrier →ₜ* ℂˣ := by
  letI := T.topology
  exact (T.unramifiedCharacterContinuous z).comp (T.generalLinearDeterminant n)

/-- A norm-one parameter gives a pointwise norm-one character. -/
theorem norm_unramifiedCharacter (z : ℂˣ) (hz : ‖(z : ℂ)‖ = 1) (a : F.Carrierˣ) :
    ‖(T.unramifiedCharacter z a : ℂ)‖ = 1 := by
  simp [norm_zpow, hz]

theorem norm_determinantUnramifiedCharacter (n : ℕ) (z : ℂˣ)
    (hz : ‖(z : ℂ)‖ = 1) (g : GeneralLinear n F.Carrier) :
    ‖(T.determinantUnramifiedCharacter n z g : ℂ)‖ = 1 :=
  T.norm_unramifiedCharacter z hz (GeneralLinear.determinant g)

/-- The unitary characters are exactly those with norm-one uniformizer value. -/
theorem norm_unramifiedCharacter_iff (z : ℂˣ) :
    (∀ a : F.Carrierˣ, ‖(T.unramifiedCharacter z a : ℂ)‖ = 1) ↔ ‖(z : ℂ)‖ = 1 := by
  constructor
  · intro h
    simpa only [T.unramifiedCharacter_uniformizer] using h T.uniformizerUnit
  · exact T.norm_unramifiedCharacter z

end Langlands.PadicField.TopologicalData
