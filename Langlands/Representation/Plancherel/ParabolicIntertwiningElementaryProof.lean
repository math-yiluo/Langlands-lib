import Langlands.Representation.Plancherel.ParabolicIntertwiningElementaryStatement
import Langlands.Representation.Plancherel.ParabolicRadicalUnimodularity
import Langlands.Representation.Plancherel.StandardIntertwiningFullDomainTransport

/-! # Elementary structural and representative-transport proofs -/

namespace Langlands.Plancherel

universe u uV uW

/-- The elementary unimodularity and full-domain transport assertions. -/
theorem parabolicIntertwiningElementaryStatement :
    ParabolicIntertwiningElementaryStatement.{u, uV, uW} := by
  refine ⟨parabolicRadical_isUnimodular, ?_, ?_⟩
  · intro G _ _ _ _ P M U U' h hU _ ν A B e
    exact StandardIntertwining.domain_eq_top_iff_equiv h hU U' ν e
  · intro G _ _ _ _ P P' M U U' h hU h' hU' _ _ _ _ _ _ _ ν μU' μI _ _ _ _ _ _
      hν hM hsq A B hfullA e
    exact StandardIntertwining.fullSourceIntertwiner_equivalent_representative
      h hU U' ν h' hU' μU' μI hν hM hsq hfullA e

end Langlands.Plancherel
