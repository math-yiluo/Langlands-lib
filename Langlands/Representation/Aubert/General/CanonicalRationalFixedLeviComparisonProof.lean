import Langlands.Representation.Aubert.General.CanonicalRationalComplexTargetBridgesProof
import Langlands.Representation.Aubert.General.RationalFixedLeviComparisonProof

/-! # Proof of the canonical fixed-Levi comparison -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- The fixed-Levi equality of Aubert's erratum for the canonical actual families. -/
theorem canonicalRationalFixedLeviComparison :
    CanonicalRationalFixedLeviComparisonStatement.{u, v} :=
  canonicalRationalFixedLeviComparison_of_rational.{u, v}
    rationalFixedLeviComparison.{u, v}

end Langlands.Aubert.General.RationalPointFamily
