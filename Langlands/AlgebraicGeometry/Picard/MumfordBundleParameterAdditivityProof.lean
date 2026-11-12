import Langlands.AlgebraicGeometry.Picard.MumfordBundleParameterAdditivityStatement
import Langlands.AlgebraicGeometry.Picard.MumfordParameterAxes
import Langlands.AlgebraicGeometry.Picard.RelativeRigidifiedCubeProof

/-! # Parameter additivity of the actual relative Mumford family -/

universe u

namespace Langlands.AbelianScheme

/-- The actual normalized Mumford family is additive in its parameter, as an
equality of full rigidified family classes over the parameter product. -/
theorem mumfordBundleParameterAdditivity :
    MumfordBundleParameterAdditivityStatement.{u} := by
  intro preservation S _ A L M evaluation
  apply relativeRigidifiedCube S A A A
  · exact mumfordBundleParameterAdditivity_firstAxis A preservation L M evaluation
  · exact mumfordBundleParameterAdditivity_secondAxis A preservation L M evaluation

end Langlands.AbelianScheme
