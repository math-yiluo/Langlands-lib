import Langlands.Geometry.Building.AlgebraicSU3RootCoordinatesExistenceStatement
import Langlands.Geometry.Building.AlgebraicSU3RootCoordinatesConstruction
import Langlands.GroupScheme.Rational.AdjacentSimpleRootSpecialLinearProof

/-! # Existence of algebraic SU3 rank-one coordinates at multipliable roots: proof -/

universe u

namespace Langlands.Geometry.Building

/-- **SU3 half of the algebraic rank-one coordinates.** Every indivisible multipliable relative
root of a supplied maximal split torus, with a torus centralizer presentation, has coherent
opposite-root SU3 coordinates whose standard Weyl element normalizes the split torus.

This proves `AlgebraicSU3RootCoordinatesExistenceStatement` at every universe, by applying the
conditional construction `algebraicSU3RootCoordinatesExistence_of_product_of_adjacent` to the
published theorems `splitRelativeRootGroupProduct` and
`Langlands.GroupScheme.adjacentSimpleRootSpecialLinear`. -/
theorem algebraicSU3RootCoordinatesExistence :
    AlgebraicSU3RootCoordinatesExistenceStatement.{u} :=
  algebraicSU3RootCoordinatesExistence_of_product_of_adjacent splitRelativeRootGroupProduct
    Langlands.GroupScheme.adjacentSimpleRootSpecialLinear

end Langlands.Geometry.Building
