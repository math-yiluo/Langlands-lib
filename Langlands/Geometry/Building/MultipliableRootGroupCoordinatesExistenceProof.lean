import Langlands.Geometry.Building.MultipliableRootGroupCoordinatesReduction
import Langlands.Geometry.Building.AlgebraicSU3RootCoordinatesExistenceProof
import Langlands.GroupScheme.Examples.SU3RootUnitaryChartUpgrade

/-! # Existence of valued scheme-level unitary coordinates of multipliable root groups: proof -/

universe u

namespace Langlands.Geometry.Building

/-- **Valued unitary coordinates of multipliable root groups.** For a nonarchimedean local
field `F`, an affine group scheme `G` over the maximal unramified field `K` with building data
`B`, and a relative root `b` with `2 • b` a relative root, there are valued scheme-level unitary
coordinates `R_{E/K} U_{L/E} ⟶ G` of the root group `U_b`.

This proves `MultipliableRootGroupCoordinatesExistenceStatement` at every universe, by applying
the conditional reduction `multipliableRootGroupCoordinatesExistence_of_algebraicSU3` to the
published theorems `algebraicSU3RootCoordinatesExistence` and
`Langlands.GroupScheme.RelativeRoot.unitaryChartUpgrade`. -/
theorem multipliableRootGroupCoordinatesExistence :
    MultipliableRootGroupCoordinatesExistenceStatement.{u} :=
  multipliableRootGroupCoordinatesExistence_of_algebraicSU3 algebraicSU3RootCoordinatesExistence
    Langlands.GroupScheme.RelativeRoot.unitaryChartUpgrade

end Langlands.Geometry.Building
