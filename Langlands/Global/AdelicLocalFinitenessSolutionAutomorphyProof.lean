import Langlands.Automorphic.GroupSchemeEnvelopingCenterConjugationProof
import Langlands.Global.AdelicLocalFinitenessCenterStability
import Langlands.Global.AdelicLocalFinitenessProof
import Langlands.Global.AdelicLocalFinitenessSolutionAutomorphy

universe u

namespace Langlands.Global

open Langlands.Automorphic.GroupSchemeFunctions

/-- Solutions of the admissible local-finiteness system with left compact-finite
kernels are automorphic forms. -/
theorem localFinitenessSolutionAutomorphy : LocalFinitenessSolutionAutomorphyStatement.{u} :=
  localFinitenessSolutionAutomorphy_of uniformGrowthLocalFiniteness
    (localFinitenessCenterStability_of adelicEnvelopingCenterConjugation)

end Langlands.Global
