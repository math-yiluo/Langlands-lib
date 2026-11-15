import Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianReductionProof
import Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionProof
import Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyProof

/-! # Representability on locally noetherian tests of fppf sheaves presented by a flat proper
equivalence relation

Proof of `FppfQuotientLocallyNoetherianStatement`: the published reduction
`FppfQuotientLocallyNoetherianReductionStatement` applied to the effective quotient theorem
`FlatProperEquivalenceRelationQuotientStatement` (Nitsure, Theorem 6.8), which is in turn the
published reduction `FlatProperEquivalenceRelationQuotientReductionStatement` applied to the
published Hilbert scheme theorem `HilbertSchemeUniversalFamilyStatement`. -/

universe u

namespace Langlands.AlgebraicGeometry

/-- An fppf sheaf over a noetherian affine base, presented as the quotient of an
H-quasi-projective scheme by a flat proper equivalence relation, is represented on locally
noetherian tests by an H-quasi-projective scheme. -/
theorem fppfQuotientLocallyNoetherian : FppfQuotientLocallyNoetherianStatement.{u} :=
  FppfQuotientLocallyNoetherianReduction.fppfQuotientLocallyNoetherianReduction
    (FlatEquivalenceRelation.flatProperEquivalenceRelationQuotient_of_hilbertScheme
      HilbertSchemeUniversalFamily.hilbertSchemeUniversalFamily)

end Langlands.AlgebraicGeometry
