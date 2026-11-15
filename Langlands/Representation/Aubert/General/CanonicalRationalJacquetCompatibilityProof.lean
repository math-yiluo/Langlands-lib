import Langlands.Representation.Aubert.General.CanonicalRationalTargetBridgesProof
import Langlands.Representation.Aubert.General.RationalJacquetCompatibilityProof

/-! # Proof of canonical Jacquet compatibility -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Théorème 1.7 (2), second equation, for the canonical actual families. -/
theorem canonicalRationalJacquetCompatibility :
    CanonicalRationalJacquetCompatibilityStatement.{u, v} :=
  canonicalRationalJacquetCompatibility_of_rational.{u, v}
    rationalJacquetCompatibility.{u, v}

end Langlands.Aubert.General.RationalPointFamily
