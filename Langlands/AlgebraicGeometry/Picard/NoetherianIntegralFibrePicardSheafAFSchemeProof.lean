import Langlands.AlgebraicGeometry.Picard.NoetherianIntegralFibrePicardSheafAFSchemeAssembly
import Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionProof
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesProof
import Langlands.AlgebraicGeometry.Picard.ProperFlatIntegralLinearSystemProof
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorBaseChangeProof
import Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianReductionProof
import Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientReductionProof
import Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyProof

/-! # The Picard scheme of an integral-fibre family over a noetherian ring (proof)

Proof of `NoetherianIntegralFibrePicardSheafAFSchemeStatement` (Kleiman, *The Picard scheme*,
Theorem 4.8(2)). -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- Kleiman, Theorem 4.8(2): for a pointed proper flat family with geometrically integral fibres
over a noetherian ring, with an ample line bundle on the total space, the fppf Picard class sheaf
is represented by a scheme in which every finite set of points lies in an affine open. -/
theorem noetherianIntegralFibrePicardSheafAFScheme :
    NoetherianIntegralFibrePicardSheafAFSchemeStatement.{u} :=
  noetherianIntegralFibrePicardSheafAFScheme_of_piecesRepresentability
    (PicardHilbertPiecesReduction.picardHilbertPiecesRepresentabilityReduction
      relativeEffectiveDivisorHilbertPieces properFlatIntegralLinearSystem
      (FppfQuotientLocallyNoetherianReduction.fppfQuotientLocallyNoetherianReduction
        (FlatEquivalenceRelation.flatProperEquivalenceRelationQuotient_of_hilbertScheme
          HilbertSchemeUniversalFamily.hilbertSchemeUniversalFamily))
      RelativeEffectiveDivisorBaseChangeProof.relativeEffectiveDivisorBaseChange)

end Langlands.AlgebraicGeometry.Picard
