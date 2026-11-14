import Langlands.AlgebraicGeometry.HilbertSchemeUniversalFamilyStatement
import Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientStatement

/-! # Reduction of effective quotients by flat proper equivalence relations to the Hilbert
scheme -/

universe u

namespace Langlands.AlgebraicGeometry

/-- The Hilbert scheme of a projective flat family, with its universal closed subscheme on all
test schemes and its H-projective Hilbert-polynomial pieces
(`HilbertSchemeUniversalFamilyStatement`), yields an effective H-quasi-projective quotient of
every H-quasi-projective scheme over a noetherian ring by a flat proper equivalence relation
(`FlatProperEquivalenceRelationQuotientStatement`). -/
def FlatProperEquivalenceRelationQuotientReductionStatement : Prop :=
  HilbertSchemeUniversalFamilyStatement.{u} →
    FlatProperEquivalenceRelationQuotientStatement.{u}

end Langlands.AlgebraicGeometry
