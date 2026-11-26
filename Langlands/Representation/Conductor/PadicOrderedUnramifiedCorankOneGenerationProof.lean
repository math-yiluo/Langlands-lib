import Langlands.Representation.Conductor.OrderedUnramifiedGenerationFromPremises
import Langlands.Representation.RankinSelberg.PadicTemperedTypePremises

/-!
# Jacquet's Lemma 3 over p-adic fields

Over a p-adic field with its canonical structures, the three premises of
`orderedUnramifiedCorankOneGenerationAt_of_premises` are proved by the Library's p-adic
results (`RankinSelberg.PadicTemperedType`): the classification with the identification
of Whittaker models, the pole bound (8.4) and the tail divisibility (9.3). This proves
`PadicOrderedUnramifiedCorankOneGenerationStatement`.
-/

noncomputable section

namespace Langlands.Conductor

universe uF uV

/-- Jacquet 2012, Lemma 3, over every p-adic field. -/
theorem padicOrderedUnramifiedCorankOneGeneration :
    PadicOrderedUnramifiedCorankOneGenerationStatement.{uF, uV} := by
  intro p _ K
  let := K.canonicalTopologicalData.topology
  let := K.canonicalTopologicalData.valuativeRel
  let := K.canonicalTopologicalData.localField
  exact orderedUnramifiedCorankOneGenerationAt_of_premises K.Carrier
    (RankinSelberg.PadicTemperedType.genericStandardModule.{uF, uV} K)
    (RankinSelberg.PadicTemperedType.temperedPoleBound.{uF, max uF uV, uF} K)
    (RankinSelberg.PadicTemperedType.inducedTailLFactorAt.{uF, uF, max uF uV, max uF uV} K)
    (RankinSelberg.PadicTemperedType.inducedTailLFactorAt.{uF, max uF uV, uF, uF} K)

end Langlands.Conductor
