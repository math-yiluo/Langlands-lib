import Langlands.Group.GL.Padic
import Langlands.LocalField.Normalization.Proof
import Langlands.Topology.CompactNormCharacter
import Mathlib.Topology.Algebra.ValuativeRel.ValuativeTopology

/-!
# The residue-normalized determinant character

The value is the actual residue-cardinality-normalized absolute value of the
usual determinant. No unadjusted spectral norm is substituted.
-/

noncomputable section

open scoped NNReal

namespace Langlands.PadicField

universe u

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p}

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

theorem determinantNorm_eq_residue_pow (n : ℕ) (g : GeneralLinear n F.Carrier) :
    ((T.determinantNorm n g : ℝ≥0) : ℝ) =
      (T.residueCardinality : ℝ) ^ (-T.ord (GeneralLinear.determinant g : F.Carrier)) :=
  T.normalizedAbs_of_ne_zero (GeneralLinear.determinant g).ne_zero

theorem determinantNorm_eq_canonicalNorm_pow_degree
    (n : ℕ) (g : GeneralLinear n F.Carrier) :
    ((T.determinantNorm n g : ℝ≥0) : ℝ) =
      F.canonicalNorm (GeneralLinear.determinant g : F.Carrier) ^
        Module.finrank (Padic p) F.Carrier :=
  T.normalizedAbs_eq_canonicalNorm_pow_degree _

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
  rw [T.topology_eq_canonicalNormTopology]
  let := F.canonicalNormedField
  apply Continuous.subtype_mk
  change Continuous (fun x : F.Carrier => T.normalizedAbs x)
  simp_rw [T.normalizedAbs_eq_canonicalNorm_pow_degree]
  exact continuous_norm.pow _

theorem continuous_normalizedAbsUnits :
    letI := T.topology
    Continuous T.normalizedAbsUnits := by
  let := T.topology
  exact T.continuous_normalizedAbsHom.units_map

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

/-- The normalized determinant is continuous for the actual matrix-unit topology. -/
def determinantNormContinuous (n : ℕ) :
    letI := T.topology
    ContinuousMonoidHom (GeneralLinear n F.Carrier) ℝ≥0ˣ := by
  letI := T.topology
  exact
    { toMonoidHom := T.determinantNorm n
      continuous_toFun :=
        T.continuous_normalizedAbsUnits.comp (T.generalLinearDeterminant n).continuous }

/-- The existing continuous positive-character theorem applies to the actual
determinant norm on every compact matrix subgroup. -/
theorem determinantNorm_eq_one_of_mem_compact (r : ℕ) :
    letI := T.topology
    ∀ (J : Subgroup (GeneralLinear r F.Carrier)),
      IsCompact (J : Set (GeneralLinear r F.Carrier)) →
      ∀ g ∈ J, T.determinantNorm r g = 1 := by
  let := T.topology
  intro J hJ g hg
  exact RankinSelberg.LastRowReduction.eq_one_of_isCompact
    (T.determinantNorm r) (T.determinantNormContinuous r).continuous J hJ hg

/-- The norm character has open kernel; this is proved for every supplied realization. -/
theorem isOpen_ker_determinantNorm (n : ℕ) :
    letI := T.generalLinearTopology n
    IsOpen ((T.determinantNorm n).ker : Set (GeneralLinear n F.Carrier)) := by
  let := T.topology
  change IsOpen (GeneralLinear.determinant ⁻¹' (T.normalizedAbsUnits.ker : Set F.Carrierˣ))
  exact T.isOpen_ker_normalizedAbsUnits.preimage (T.generalLinearDeterminant n).continuous

/-- Two compatible local-field realizations give the same normalized norm character. -/
theorem normalizedAbsHom_eq (U : F.TopologicalData) :
    T.normalizedAbsHom = U.normalizedAbsHom := by
  ext x
  change T.normalizedAbs x = U.normalizedAbs x
  rw [T.normalizedAbs_eq_canonicalNorm_pow_degree, U.normalizedAbs_eq_canonicalNorm_pow_degree]

theorem determinantNorm_eq (U : F.TopologicalData) (n : ℕ) :
    T.determinantNorm n = U.determinantNorm n := by
  simp only [determinantNorm, normalizedAbsUnits, T.normalizedAbsHom_eq U]

end TopologicalData

/-- The normalized determinant character for every algebraic p-adic field. -/
abbrev canonicalDeterminantNorm (F : PadicField.{u} p) (n : ℕ) :
    GeneralLinear n F.Carrier →* ℝ≥0ˣ :=
  F.canonicalTopologicalData.determinantNorm n

/-- Its open kernel uses the canonical, actual general-linear topology. -/
theorem isOpen_ker_canonicalDeterminantNorm (F : PadicField.{u} p) (n : ℕ) :
    letI := F.canonicalGeneralLinearTopology n
    IsOpen ((F.canonicalDeterminantNorm n).ker : Set (GeneralLinear n F.Carrier)) :=
  F.canonicalTopologicalData.isOpen_ker_determinantNorm n

end Langlands.PadicField
