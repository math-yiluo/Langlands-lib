import Langlands.ClassFieldTheory.Local.CommonClosureExistenceGeometricReduction
import Langlands.ClassFieldTheory.Local.FiniteGeometricCupArtinComparisonProof

/-! # Existence of normalized actual common-closure reciprocity -/

namespace Langlands.LocalClassField

universe u

/-- A normalized coherent reciprocity system exists on all actual finite
intermediate fields of the common algebraic closure. -/
theorem commonClosureReciprocityExistence :
    CommonClosureReciprocityExistence.{u} :=
  commonClosureReciprocityExistence_of_finiteGeometricCupComparison
    ClassFieldTheory.Local.finiteGeometricCupArtinCharacterComparison

end Langlands.LocalClassField
