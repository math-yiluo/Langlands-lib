import Langlands.Geometry.Building.TorusFiltration.ShallowModelProof
import Langlands.Geometry.Building.TorusFiltration.FunctorialityProof
import Langlands.Geometry.Building.TorusFiltration.OrderProof
import Langlands.Geometry.Building.TorusFiltration.ConnectedModelProof
import Langlands.Geometry.Building.TorusFiltration.CongruenceProof
import Langlands.Geometry.Building.TorusFiltration.WeaklyInducedProof

/-! # Structural properties of the minimal congruent torus filtration -/

universe u

namespace Langlands.Geometry.Building

theorem minimalCongruentStructural : MinimalCongruentStructuralStatements.{u} :=
  ⟨minimalCongruentShallowModel, minimalCongruentFunctoriality, minimalCongruentOrder,
    minimalCongruentConnectedModel, minimalCongruentCongruence, minimalCongruentWeaklyInduced⟩

end Langlands.Geometry.Building
