import Langlands.LocalField.Definitions
import Mathlib.Algebra.CharP.Basic
import Mathlib.FieldTheory.Finite.Basic

/-!
# Arithmetic data of a specified p-adic local field

The integer and residue rings below are those of the valuation supplied in
`TopologicalData`. The arithmetic and absolute-value data use that valuation
and its ordered discrete value group throughout.
-/

namespace Langlands.PadicField.TopologicalData

open scoped WithZero

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

/-- The integer ring of the specified valuation. -/
noncomputable abbrev Integers :=
  letI := T.valuativeRel
  (ValuativeRel.valuation F.Carrier).integer

/-- The residue field of the actual valuation integer ring. -/
abbrev ResidueField := IsLocalRing.ResidueField T.Integers

/-- The residue-field quotient map. -/
noncomputable abbrev residue : T.Integers →+* T.ResidueField :=
  IsLocalRing.residue T.Integers

/-- The specified base embedding restricts to the actual valuation rings. -/
noncomputable def baseIntegerMap :
    (ValuativeRel.valuation (Padic p)).integer →+* T.Integers := by
  letI := T.valuativeRel
  letI := T.valuativeExtension
  refine ((algebraMap (Padic p) F.Carrier).comp
    (ValuativeRel.valuation (Padic p)).integer.subtype).codRestrict T.Integers ?_
  intro x
  change ValuativeRel.valuation F.Carrier (algebraMap (Padic p) F.Carrier x.val) ≤ 1
  rw [← (ValuativeRel.valuation F.Carrier).vle_one_iff]
  have hx : (x : Padic p) ≤ᵥ 1 :=
    ((ValuativeRel.valuation (Padic p)).vle_one_iff).mpr x.property
  simpa only [map_one] using
    (ValuativeExtension.vle_iff_vle (A := Padic p) (B := F.Carrier) x.val 1).mpr hx

/-- The extension of the actual valuation integer rings, with explicit scalars. -/
noncomputable abbrev integerAlgebra :
    Algebra (ValuativeRel.valuation (Padic p)).integer T.Integers :=
  T.baseIntegerMap.toAlgebra

/-- The characteristic certificate used to construct the residue scalar map. -/
abbrev residueCharP : CharP T.ResidueField p := by
  let := T.valuativeRel
  let := T.valuativeExtension
  apply (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr
  rw [← map_natCast T.residue, IsLocalRing.residue_eq_zero_iff]
  rw [IsLocalRing.mem_maximalIdeal]
  change ¬IsUnit (p : T.Integers)
  rw [Valuation.Integer.not_isUnit_iff_valuation_lt_one]
  change ValuativeRel.valuation F.Carrier (p : F.Carrier) < 1
  rw [← (ValuativeRel.valuation F.Carrier).vlt_one_iff]
  have hp : (p : Padic p) <ᵥ 1 := by
    rw [(ValuativeRel.valuation (Padic p)).vlt_one_iff]
    exact Padic.valuation_p_lt_one _
  simpa only [map_natCast, map_one] using
    (ValuativeExtension.vlt_iff_vlt (A := Padic p) (B := F.Carrier)).mpr hp

/-- The canonical map from the prime field to the actual residue field. -/
noncomputable def residueScalarMap : ZMod p →+* T.ResidueField :=
  letI := T.residueCharP
  ZMod.castHom (dvd_refl p) T.ResidueField

/-- The scalar structure used for the residue degree; it is explicit data. -/
noncomputable abbrev residueAlgebra : Algebra (ZMod p) T.ResidueField :=
  T.residueScalarMap.toAlgebra

/-- The actual residue cardinality, independent of a choice of enumeration. -/
noncomputable def residueCardinality : ℕ := Nat.card T.ResidueField

/-- Residue degree over the prime field, using the specified scalar map. -/
noncomputable def residueDegree : ℕ :=
  letI := T.residueAlgebra
  Module.finrank (ZMod p) T.ResidueField

/-- The multiplicative discrete valuation, with a zero value at zero. -/
noncomputable def discreteValuation : Valuation F.Carrier ℤᵐ⁰ :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  (ValuativeRel.valuation F.Carrier).map
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier).toMonoidWithZeroHom
    (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier).strictMono.monotone

/-- A chosen element of valuation `exp (-1)`, hence a uniformizer. -/
noncomputable def uniformizer : F.Carrier := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact (ValuativeRel.valuation_surjective
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F.Carrier).symm
      (WithZero.exp (-1)))).choose

/-- The normalized additive order; the convention at zero is `0`.
Statements using this integer-valued function must account for zero explicitly. -/
noncomputable def ord (x : F.Carrier) : ℤ := -WithZero.log (T.discreteValuation x)

/-- Absolute ramification index measured by the order of the base prime. -/
noncomputable def ramificationIndex : ℕ := (T.ord (p : F.Carrier)).toNat

/-- Residue-cardinality normalization, explicitly zero at zero. -/
noncomputable def normalizedAbs (x : F.Carrier) : ℝ := by
  classical
  exact if x = 0 then 0 else (T.residueCardinality : ℝ) ^ (-T.ord x)

end Langlands.PadicField.TopologicalData
