import Langlands.Geometry.Building.AlgebraicSU3RootCoordinatesConstruction
import Langlands.GroupScheme.Rational.AdjacentSimpleRootSpecialLinearProof

/-! # Existence of coherent algebraic rank-one coordinates: proof -/

universe u

namespace Langlands.Geometry.Building

/-- **Coherent algebraic SL2/SU3 rank-one coordinates exist.** Every indivisible relative root
of a connected reductive group, relative to a maximal split torus whose centralizer is a
torus, has coherent opposite-root `SL₂` or `SU₃` coordinates, and the standard Weyl element
normalizes the maximal split torus. -/
theorem algebraicRankOneCoordinatesExistence :
    AlgebraicRankOneCoordinatesExistenceStatement.{u} :=
  algebraicRankOneCoordinatesExistence_of_adjacent
    Langlands.GroupScheme.adjacentSimpleRootSpecialLinear

end Langlands.Geometry.Building
