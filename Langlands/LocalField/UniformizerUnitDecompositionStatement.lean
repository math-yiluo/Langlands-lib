import Langlands.LocalField.ResidueNormalization

/-! # Decomposition of a field unit by a uniformizer -/

namespace Langlands.LocalField

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

/-- For each field unit of order one, multiplication of an integral unit by an
integer power of that uniformizer parametrizes the field units uniquely. -/
def UniformizerUnitDecompositionStatement : Prop :=
  ∀ π : Fˣ, FML.ord F (π : F) = 1 →
    Function.Bijective fun pair : FML.unitGroup F × ℤ => (pair.1 : Fˣ) * π ^ pair.2

end Langlands.LocalField
