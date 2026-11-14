import Langlands.AlgebraicGeometry.FppfQuotientLocallyNoetherianStatement
import Langlands.AlgebraicGeometry.FlatProperEquivalenceRelationQuotientStatement

/-! # Reduction of the fppf quotient on locally noetherian tests to effective quotients by
flat proper equivalence relations -/

universe u

namespace Langlands.AlgebraicGeometry

/-- An effective quotient of every H-quasi-projective scheme over a noetherian ring by a flat
proper equivalence relation (`FlatProperEquivalenceRelationQuotientStatement`) yields the
representability on locally noetherian tests of every fppf sheaf receiving a locally surjective
map from such a scheme whose relation is detected on locally noetherian tests
(`FppfQuotientLocallyNoetherianStatement`). -/
def FppfQuotientLocallyNoetherianReductionStatement : Prop :=
  FlatProperEquivalenceRelationQuotientStatement.{u} →
    FppfQuotientLocallyNoetherianStatement.{u}

end Langlands.AlgebraicGeometry
