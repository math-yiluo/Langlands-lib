import Langlands.Global.AdelicSpacePointTopologyProof
import Langlands.Global.AdelicSpaceSpreadIndependenceProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceFilteredRingPointProof

/-!
# Adelic points of separated algebraic spaces over global fields

Conrad, printed p.17: the claims of `AdelicSpacePointTopologyStatement`, for global fields of
both characteristics.
-/

universe u

namespace Langlands.Global

/-- **Conrad, printed p.17.** For a separated algebraic space of finite type over the ring of
`S`-integers of a global field, the adelic points carry the colimit topology of the level
topologies, with open stage embeddings, local compactness, the Hausdorff property and second
countability, functoriality, and agreement with the scheme construction; every separated
algebraic space of finite type over the global field has a separated model of finite type over
some ring of `S`-integers, and the resulting topology on its adelic points does not depend on the
model. -/
theorem adelicSpacePointTopology : AdelicSpacePointTopologyStatement.{u} :=
  AdelicSpacePointTopologyProof.adelicSpacePointTopology_of_spread
    Langlands.AlgebraicGeometry.AlgebraicSpace.spaceFilteredRingPointComparison
    AdelicSpaceSpreadIndependenceProof.curvePlaceSpaceSpread
    AdelicSpaceSpreadIndependenceProof.numberFieldSpaceSpread

end Langlands.Global
