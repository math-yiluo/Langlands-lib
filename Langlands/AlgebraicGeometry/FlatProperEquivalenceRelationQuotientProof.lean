import Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionProof
import Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyProof

/-! # Effective quotients by flat proper equivalence relations: proof

Composes the reduction `FlatProperEquivalenceRelationQuotientReductionStatement` (Hilbert scheme
with universal family ⇒ quotient) with the proof of `HilbertSchemeUniversalFamilyStatement`. -/

universe u

namespace Langlands.AlgebraicGeometry

/-- Every H-quasi-projective scheme over a noetherian ring has an effective H-quasi-projective
quotient by a flat proper equivalence relation (Altman–Kleiman; Nitsure, Theorem 6.8). -/
theorem flatProperEquivalenceRelationQuotient :
    FlatProperEquivalenceRelationQuotientStatement.{u} :=
  FlatEquivalenceRelation.flatProperEquivalenceRelationQuotient_of_hilbertScheme
    HilbertSchemeUniversalFamily.hilbertSchemeUniversalFamily

end Langlands.AlgebraicGeometry
