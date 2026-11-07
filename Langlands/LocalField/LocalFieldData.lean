import Langlands.LocalField.ResidueNormalization
import Langlands.HarmonicAnalysis.GeneralScalarHaarScalingProof
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Explicit data for an arbitrary nonarchimedean local field -/

open scoped WithZero

namespace Langlands

universe u

/-- A supplied nonarchimedean local-field topology and valuation, without a
characteristic or a choice of base field. -/
structure LocalFieldData (F : Type u) [Field F] where
  [topology : TopologicalSpace F]
  [valuativeRel : ValuativeRel F]
  [localField : IsNonarchimedeanLocalField F]

namespace LocalFieldData

variable {F : Type u} [Field F]

/-- Package the ambient topology, valuation and local-field certificate. -/
def ofInstances (F : Type u) [Field F] [TopologicalSpace F] [ValuativeRel F]
    [IsNonarchimedeanLocalField F] : LocalFieldData F where
  topology := inferInstance
  valuativeRel := inferInstance
  localField := inferInstance

variable (T : LocalFieldData F)

/-- The integer ring of the supplied valuation. -/
noncomputable abbrev Integers :=
  letI := T.valuativeRel
  (ValuativeRel.valuation F).integer

/-- The residue field of the actual integer ring. -/
abbrev ResidueField := IsLocalRing.ResidueField T.Integers

/-- The residue quotient map. -/
noncomputable abbrev residue : T.Integers →+* T.ResidueField :=
  IsLocalRing.residue T.Integers

/-- The cardinality of the actual residue field. -/
noncomputable def residueCardinality : ℕ := Nat.card T.ResidueField

/-- The normalized multiplicative valuation in the canonical discrete group. -/
noncomputable def discreteValuation : Valuation F ℤᵐ⁰ :=
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  FML.normalizedMultiplicativeValuation F

/-- A chosen element of discrete valuation `exp (-1)`. -/
noncomputable def uniformizer : F := by
  letI := T.topology
  letI := T.valuativeRel
  letI := T.localField
  exact (ValuativeRel.valuation_surjective
    ((IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt F).symm
      (WithZero.exp (-1)))).choose

/-- Integer order, with the explicit convention `ord 0 = 0`.
Every use as a valuation order must account for zero separately. -/
noncomputable def ord (x : F) : ℤ := -WithZero.log (T.discreteValuation x)

/-- The residue-normalized absolute value, explicitly zero at zero. -/
noncomputable def normalizedAbs (x : F) : ℝ := by
  classical
  exact if x = 0 then 0 else (T.residueCardinality : ℝ) ^ (-T.ord x)

end LocalFieldData
end Langlands
