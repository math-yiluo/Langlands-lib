import Langlands.ClassFieldTheory.Local.UpperReciprocityNormReduction
import Langlands.ClassFieldTheory.Local.NormUnitImageCardinalityProof

/-! # Finite upper ramification compatibility of local reciprocity -/

namespace Langlands.LocalClassField

universe u

/-- Finite local reciprocity identifies higher unit images with upper
ramification groups and gives the norm and finite-character conductor criteria. -/
theorem finiteUpperReciprocityTheorems : FiniteUpperReciprocityTheorems.{u} :=
  finiteUpperReciprocityTheorems_of_normCardinality
    NormUnitImage.finiteAbelianNormUnitImageCardinality.{u, u}

end Langlands.LocalClassField
