import Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyStatement
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveCartierLocusStatement
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorHilbertPiecesStatement

/-! # Reduction of the representability of relative effective divisors to the Hilbert scheme
with its universal family and the openness of the relative effective Cartier locus -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- The Hilbert scheme of a projective flat family on all test schemes, with its universal
closed subscheme and H-projective Hilbert-polynomial pieces
(`HilbertSchemeUniversalFamilyStatement`), together with the openness of the relative effective
Cartier locus of a flat closed subscheme of a proper flat family over a locally noetherian base
(`RelativeEffectiveCartierLocusStatement`), yields the representability of relative effective
divisors with H-quasi-projective Hilbert-polynomial pieces
(`RelativeEffectiveDivisorHilbertPiecesStatement`). -/
def RelativeEffectiveDivisorHilbertPiecesReductionStatement : Prop :=
  HilbertSchemeUniversalFamilyStatement.{u} →
    RelativeEffectiveCartierLocusStatement.{u} →
      RelativeEffectiveDivisorHilbertPiecesStatement.{u}

end Langlands.AlgebraicGeometry.Picard
