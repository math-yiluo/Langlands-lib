import Langlands.AllFieldBZ.Group.GL.Padic
import Langlands.AllFieldBZ.LocalField.Definitions
import Langlands.Group.GL.NormalizedCharacter

/-!
# All-field port of `Langlands.Group.GL.NormalizedCharacter`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Group.GL.NormalizedCharacter` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open scoped NNReal
namespace Langlands.AllFieldBZ.LocalFieldPackage
universe u

variable {F : LocalFieldPackage.{u}}

namespace TopologicalData
variable (T : F.TopologicalData)

/-- The accepted normalized absolute value, as a nonnegative monoid-with-zero map. -/
def normalizedAbsHom : F.Carrier →*₀ ℝ≥0 where
  toFun x := ⟨T.normalizedAbs x, T.normalizedAbs_nonneg x⟩
  map_zero' := NNReal.eq T.normalizedAbs_zero
  map_one' := NNReal.eq T.normalizedAbs_one
  map_mul' x y := NNReal.eq (T.normalizedAbs_mul x y)

@[simp]
theorem normalizedAbsHom_coe (x : F.Carrier) :
    (T.normalizedAbsHom x : ℝ) = T.normalizedAbs x := rfl

/-- Restrict the genuine normalized absolute value to the multiplicative group. -/
def normalizedAbsUnits : F.Carrierˣ →* ℝ≥0ˣ :=
  Units.map T.normalizedAbsHom.toMonoidHom

@[simp]
theorem normalizedAbsUnits_coe (a : F.Carrierˣ) :
    ((T.normalizedAbsUnits a : ℝ≥0) : ℝ) = T.normalizedAbs a := rfl

/-- The character `g ↦ |det(g)|_F` with the residue-cardinality normalization. -/
def determinantNorm (n : ℕ) : GeneralLinear n F.Carrier →* ℝ≥0ˣ :=
  T.normalizedAbsUnits.comp GeneralLinear.determinant

@[simp]
theorem determinantNorm_coe (n : ℕ) (g : GeneralLinear n F.Carrier) :
    ((T.determinantNorm n g : ℝ≥0) : ℝ) =
      T.normalizedAbs (GeneralLinear.determinant g : F.Carrier) := rfl

@[simp]
theorem determinantNorm_scalar (n : ℕ) (a : F.Carrierˣ) :
    T.determinantNorm n (GeneralLinear.scalar a) = T.normalizedAbsUnits a ^ n := by
  change T.normalizedAbsUnits (Matrix.GeneralLinearGroup.det
    (Matrix.GeneralLinearGroup.scalar (Fin n) a)) = _
  rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow]

/-- The norm-one locus is exactly the valuation-one locus, including the zero case. -/
theorem normalizedAbs_eq_one_iff_discreteValuation (x : F.Carrier) :
    T.normalizedAbs x = 1 ↔ T.discreteValuation x = 1 := by
  by_cases hx : x = 0
  · simp [hx, T.normalizedAbs_zero]
  have h := T.normalizedAbs_le_iff_of_ne_zero hx (one_ne_zero : (1 : F.Carrier) ≠ 0)
  have h' := T.normalizedAbs_le_iff_of_ne_zero (one_ne_zero : (1 : F.Carrier) ≠ 0) hx
  rw [T.normalizedAbs_one, map_one] at h h'
  rw [le_antisymm_iff, h, h', ← le_antisymm_iff]

theorem continuous_normalizedAbsHom :
    letI := T.topology
    Continuous T.normalizedAbsHom := by
  -- MANUAL: the p-adic proof went through the canonical norm; use the
  -- arbitrary-field continuity of the normalized absolute value instead.
  let := T.topology
  exact Continuous.subtype_mk T.continuous_normalizedAbs _

theorem isOpen_ker_normalizedAbsUnits :
    letI := T.topology
    IsOpen (T.normalizedAbsUnits.ker : Set F.Carrierˣ) := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have ho : IsOpen {x : F.Carrier | ValuativeRel.valuation F.Carrier x = 1} := by
    simpa only [Valuation.restrict_eq_one_iff] using
      (ValuativeRel.valuation F.Carrier).isOpen_sphere (r := 1) one_ne_zero
  have he (a : F.Carrierˣ) :
      a ∈ T.normalizedAbsUnits.ker ↔ ValuativeRel.valuation F.Carrier (a : F.Carrier) = 1 := by
    rw [MonoidHom.mem_ker, ← Units.val_inj, ← NNReal.coe_inj]
    change T.normalizedAbs a = 1 ↔ _
    rw [T.normalizedAbs_eq_one_iff_discreteValuation]
    change (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)
      (ValuativeRel.valuation F.Carrier (a : F.Carrier)) = 1 ↔ _
    rw [← map_one (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier)]
    exact (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier).injective.eq_iff
  convert ho.preimage Units.continuous_val using 1
  ext a
  exact he a

/-- The norm character has open kernel; this is proved for every supplied realization. -/
theorem isOpen_ker_determinantNorm (n : ℕ) :
    letI := T.generalLinearTopology n
    IsOpen ((T.determinantNorm n).ker : Set (GeneralLinear n F.Carrier)) := by
  let := T.topology
  change IsOpen (GeneralLinear.determinant ⁻¹' (T.normalizedAbsUnits.ker : Set F.Carrierˣ))
  exact T.isOpen_ker_normalizedAbsUnits.preimage (T.generalLinearDeterminant n).continuous

end TopologicalData
end Langlands.AllFieldBZ.LocalFieldPackage
