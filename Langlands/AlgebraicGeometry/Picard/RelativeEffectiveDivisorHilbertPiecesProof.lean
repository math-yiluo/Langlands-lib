import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesReductionProof
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveCartierLocusProof
import Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyProof

/-! # The scheme of relative effective divisors with H-quasi-projective Hilbert-polynomial pieces

Proof of `RelativeEffectiveDivisorHilbertPiecesStatement` (Kleiman, *The Picard scheme*,
Theorem 3.7, with the quasi-projectivity of the pieces from the proof of Theorem 4.8, p.30):
the published reduction `RelativeEffectiveDivisorHilbertPiecesReductionStatement` applied to
the published proofs of `HilbertSchemeUniversalFamilyStatement` and
`RelativeEffectiveCartierLocusStatement`. -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- **Relative effective divisors** of a projective flat family over a noetherian ring are
represented, on all test schemes, by a scheme `D` with a universal relative effective divisor and
H-quasi-projective Hilbert-polynomial pieces (Kleiman, Theorem 3.7). -/
theorem relativeEffectiveDivisorHilbertPieces :
    RelativeEffectiveDivisorHilbertPiecesStatement.{u} :=
  RelativeEffectiveDivisorHilbertPiecesReduction.relativeEffectiveDivisorHilbertPiecesReduction
    HilbertSchemeUniversalFamily.hilbertSchemeUniversalFamily
    RelativeEffectiveCartierLocus.relativeEffectiveCartierLocus

end Langlands.AlgebraicGeometry.Picard
