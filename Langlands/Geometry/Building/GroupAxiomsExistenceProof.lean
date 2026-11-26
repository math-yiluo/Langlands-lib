import Langlands.Geometry.Building.GroupAxiomsExistenceReduction
import Langlands.Geometry.Building.RootValuationBuildingConstructionProof
import Langlands.Geometry.Building.RootGroupActionAxiomProof
import Langlands.Geometry.Building.IwahoriDecompositionAxiomProof
import Langlands.Geometry.Building.IntegralModelAxiomsProof

/-! # Existence of building data satisfying the one-group axioms -/

universe u

namespace Langlands.Geometry.Building

/-- Over every nonarchimedean local field, each connected reductive group has a building
datum satisfying the one-group clauses of corrected KP Definition 4.1.26. -/
theorem groupAxiomsExistence : GroupAxiomsExistenceStatement.{u} :=
  groupAxiomsExistenceReduction rootValuationBuildingConstruction rootGroupActionAxiom
    iwahoriDecompositionAxiom integralModelAxioms

end Langlands.Geometry.Building
