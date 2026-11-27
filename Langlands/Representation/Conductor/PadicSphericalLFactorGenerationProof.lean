import Langlands.Representation.Conductor.SphericalLFactorGenerationFieldReduction
import Langlands.Representation.Conductor.PadicOrderedUnramifiedCorankOneGenerationProof

/-!
# The spherical L-factor generation facts over p-adic fields

`PadicSphericalLFactorGenerationStatement` from Jacquet's Lemma 3 over p-adic fields
(`padicOrderedUnramifiedCorankOneGeneration`), by the field-by-field reduction
`sphericalLFactorGenerationAt_of_generationAt`.
-/

noncomputable section

namespace Langlands.Conductor

universe uF uV

/-- The spherical L-factor generation facts of Jacquet 2012, section 1, over every p-adic
field. -/
theorem padicSphericalLFactorGeneration :
    PadicSphericalLFactorGenerationStatement.{uF, uV} := by
  intro p _ K
  let := K.canonicalTopologicalData.topology
  let := K.canonicalTopologicalData.valuativeRel
  let := K.canonicalTopologicalData.localField
  exact sphericalLFactorGenerationAt_of_generationAt K.Carrier
    (padicOrderedUnramifiedCorankOneGeneration.{uF, uV} p K)

end Langlands.Conductor
