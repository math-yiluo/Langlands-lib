import Langlands.Group.GL.UnramifiedCharacter
import Langlands.AllField.Group.GL.NormalizedCharacterSupplement
import Langlands.AllField.Group.GL.UnramifiedCharacter
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

/-- All complex values are allowed; there is no real-power or unitary restriction. -/
def unramifiedCharacter (z : ℂˣ) : Fˣ →* ℂˣ :=
  (zpowersHom ℂˣ z).comp T.ordUnits

@[simp]
theorem unramifiedCharacter_apply (z : ℂˣ) (a : Fˣ) :
    T.unramifiedCharacter z a = z ^ T.ord (a : F) := rfl

theorem ker_ordUnits_le_ker_unramifiedCharacter (z : ℂˣ) :
    T.ordUnits.ker ≤ (T.unramifiedCharacter z).ker := by
  intro a ha
  change T.ordUnits a = 1 at ha
  change (zpowersHom ℂˣ z) (T.ordUnits a) = 1
  rw [ha, map_one]

theorem isOpen_ker_unramifiedCharacter (z : ℂˣ) :
    letI := T.topology
    IsOpen ((T.unramifiedCharacter z).ker : Set Fˣ) := by
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
    Fˣ →ₜ* ℂˣ := by
  letI := T.topology
  exact { toMonoidHom := T.unramifiedCharacter z
          continuous_toFun := T.continuous_unramifiedCharacter z }

/-- The actual determinant pullback of the unramified field character. -/
def determinantUnramifiedCharacter (n : ℕ) (z : ℂˣ) :
    GeneralLinear n F →* ℂˣ :=
  (T.unramifiedCharacter z).comp GeneralLinear.determinant

@[simp]
theorem determinantUnramifiedCharacter_apply (n : ℕ) (z : ℂˣ)
    (g : GeneralLinear n F) :
    T.determinantUnramifiedCharacter n z g =
      z ^ T.ord (GeneralLinear.determinant g : F) := rfl

theorem isOpen_ker_determinantUnramifiedCharacter (n : ℕ) (z : ℂˣ) :
    letI := T.topology
    IsOpen ((T.determinantUnramifiedCharacter n z).ker : Set (GeneralLinear n F)) := by
  let := T.topology
  change IsOpen (GeneralLinear.determinant ⁻¹'
    ((T.unramifiedCharacter z).ker : Set Fˣ))
  exact (T.isOpen_ker_unramifiedCharacter z).preimage (T.generalLinearDeterminant n).continuous

end Langlands.LocalFieldData
