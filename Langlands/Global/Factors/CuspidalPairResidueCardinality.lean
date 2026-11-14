import Langlands.Global.Factors.CuspidalPairFactorData

namespace Langlands.Global.CuspidalPairFunctionalEquation.FinitePairFactorChoice

open Langlands.Global.CompletionPadic

universe u

variable {F : Type u} [Field F] [NumberField F]

theorem one_lt_residueCardinality (v : FinitePlace F) : 1 < residueCardinality v :=
  (padicField v).canonicalTopologicalData.residueCardinality_gt_one

end Langlands.Global.CuspidalPairFunctionalEquation.FinitePairFactorChoice
