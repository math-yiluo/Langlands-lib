import Langlands.Global.AdelicFunctoriality.FiniteComparisonReduction
import Langlands.Global.AdelicFunctoriality.CompletedLocalDegreeProof
import Langlands.Global.AdelicFunctoriality.NormStatement

/-! # Canonical completed tensor comparison -/

namespace Langlands.Global.AdelicFunctoriality

open NumberField IsDedekindDomain
open scoped NumberField FiniteExtension

universe u v

/-- The canonical completed tensor maps are bijections at all actual places. -/
theorem completedTensorComparison : CompletedTensorComparison.{u, v} := by
  intro K L _ _ _ _ _
  constructor
  · intro p
    apply finiteTensorMap_bijective_of_local_degree_bounds p
    intro q
    exact completedLocalDegreeLowerBound K L p q.1
  · exact infiniteTensorMap_bijective

end Langlands.Global.AdelicFunctoriality
