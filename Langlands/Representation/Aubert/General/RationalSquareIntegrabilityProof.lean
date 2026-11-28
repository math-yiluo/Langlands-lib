import Langlands.Representation.Aubert.General.RationalSquareIntegrabilityReductionProof
import Langlands.BruhatTits.SpecialCompact.JointBasisProof

/-! # Strict normalized Jacquet exponents imply square integrability

For every connected reductive group over every nonarchimedean local field, the
strict bounds on the exponents of the actual normalized standard Jacquet modules
of an admissible representation with a unitary central character imply
square integrability of all its coefficients modulo the full center
(Casselman, *Introduction to the theory of admissible representations of p-adic
reductive groups*, 1995 draft, Theorem 4.4.6, sufficiency direction). -/

universe u v

namespace Langlands.Aubert.General.RationalPointFamily

/-- Casselman's Theorem 4.4.6, sufficiency direction, on actual rational points:
admissibility, a unitary central character and strict bounds on the full-center
exponents of every actual normalized standard Jacquet module give square
integrability of every smooth coefficient modulo the full actual center, for
every Borel Haar measure on the quotient. -/
theorem rationalStrictJacquetSquareIntegrability :
    RationalStrictJacquetSquareIntegrabilityStatement.{u, v} :=
  rationalStrictJacquetSquareIntegrabilityReduction.{u, v}
    BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence.{u}

end Langlands.Aubert.General.RationalPointFamily
