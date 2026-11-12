import Langlands.Representation.Aubert.General.RationalJacquetGeometricAssembly
import Langlands.Representation.Aubert.General.RationalGeometricK0Expansion

/-!
# Proof of longest-representative Jacquet compatibility on rational points

The published target `RationalJacquetCompatibilityStatement` follows from the
published rational geometric-lemma K0 expansion through the published
assembly from that expansion to the Jacquet equation.
-/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- **Aubert Theorem 1.7(2), second equation**, for the actual rational-point
families of every connected reductive group over every nonarchimedean local
field: the exact published `RationalJacquetCompatibilityStatement`, at
independent universes. -/
theorem rationalJacquetCompatibility : RationalJacquetCompatibilityStatement.{u, v} :=
  rationalJacquetCompatibility_of_rationalGeometricK0Expansion.{u, v}
    rationalGeometricK0Expansion.{u, v}

end Langlands.Aubert.General.RationalPointFamily
