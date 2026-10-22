import Mathlib.Basic.Complex.Basic
import Mathlib.FieldTheory.Galois.Basic

/-! # Subfields of `ℂ` are fixed fields of their automorphism groups -/

namespace Langlands.Shimura

/-- Every subfield `L` of `ℂ` is the fixed field of the group of field
automorphisms of `ℂ` fixing `L` pointwise. -/
def ComplexFixedFieldStatement : Prop :=
  ∀ L : IntermediateField ℚ ℂ,
    IntermediateField.fixedField (IntermediateField.fixingSubgroup L) = L

end Langlands.Shimura
