import Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionProof
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesProof
import Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorBaseChangeProof
import Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianReductionProof
import Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionProof
import Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyProof

/-! # Quasi-projective representability of the Hilbert-polynomial pieces of the Picard sheaf

Proof of `PicardHilbertPiecesRepresentabilityStatement` (Kleiman, *The Picard scheme*, proof of
Theorem 4.8, pp.29–31): the published reduction
`PicardHilbertPiecesRepresentabilityReductionStatement` applied to the published proofs of its
four inputs. The quotient input
`FppfQuotientLocallyNoetherianStatement` is supplied by its published reduction from
`FlatProperEquivalenceRelationQuotientStatement`, itself supplied by its published reduction from
`HilbertSchemeUniversalFamilyStatement`. -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- **The pieces of the Picard sheaf** of a pointed proper flat family with geometrically
integral fibres over a noetherian ring, cut out by the given opens, are represented on locally
noetherian tests by H-quasi-projective schemes (Kleiman, proof of Theorem 4.8). -/
theorem picardHilbertPiecesRepresentability :
    PicardHilbertPiecesRepresentabilityStatement.{u} :=
  PicardHilbertPiecesReduction.picardHilbertPiecesRepresentabilityReduction
    relativeEffectiveDivisorHilbertPieces
    properFlatIntegralLinearSystem
    (FppfQuotientLocallyNoetherianReduction.fppfQuotientLocallyNoetherianReduction
      (FlatEquivalenceRelation.flatProperEquivalenceRelationQuotient_of_hilbertScheme
        HilbertSchemeUniversalFamily.hilbertSchemeUniversalFamily))
    RelativeEffectiveDivisorBaseChangeProof.relativeEffectiveDivisorBaseChange

end Langlands.AlgebraicGeometry.Picard
