import Langlands.GroupScheme.Reductive.DerivedCentralIsogenyStructuralReduction
import Langlands.GroupScheme.Reductive.RelativeCenterProof
import Langlands.GroupScheme.Torus.RelativeLargestSubtorusProof
import Langlands.GroupScheme.Reductive.FibrewiseCentralIsogenyProof

/-! # Central isogenies from the derived group and the maximal central torus -/

universe u

namespace Langlands.GroupScheme

/-- The maximal central torus exists, and the multiplication and quotient-pairing
maps in the published statement are central isogenies over every scheme base. -/
theorem reductiveDerivedCentralIsogeny : ReductiveDerivedCentralIsogenyStatement.{u} :=
  reductiveDerivedCentralIsogeny_of_structuralInputs
    reductiveRelativeCenter relativeMultiplicativeTypeLargestSubtorus
    reductiveFibrewiseCentralIsogeny

end Langlands.GroupScheme
