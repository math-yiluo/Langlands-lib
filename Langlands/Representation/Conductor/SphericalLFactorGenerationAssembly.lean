import Langlands.Representation.Conductor.SphericalCorankOneLaurentProof
import Langlands.Representation.Conductor.OrderedUnramifiedSphericalCyclicity

/-!
# Assembly of the spherical L-factor generation facts

`SphericalLFactorGenerationStatement` from Jacquet 2012, Lemma 3, for norm-ordered
parameters (`OrderedUnramifiedCorankOneGenerationStatement`). Every other input of the
reduction `sphericalLFactorGeneration_of_ordered` is proved: convergence
(`sphericalCorankOneConvergence`), the Laurent clause (`unramifiedCorankOneLaurent`), and
Jacquet's Lemmas 1 and 2 (`orderedUnramifiedSphericalCyclicity`,
`orderedUnramifiedWhittakerRealization`).
-/

namespace Langlands.Conductor

universe uF uV

/-- The spherical L-factor generation facts of Jacquet 2012, section 1, from Jacquet's
Lemma 3 for norm-ordered parameters. -/
theorem sphericalLFactorGeneration_of_generation
    (hgen : OrderedUnramifiedCorankOneGenerationStatement.{uF, uV}) :
    SphericalLFactorGenerationStatement.{uF, uV} :=
  sphericalLFactorGeneration_of_ordered sphericalCorankOneConvergence unramifiedCorankOneLaurent
    hgen orderedUnramifiedSphericalCyclicity orderedUnramifiedWhittakerRealization

end Langlands.Conductor
