import Langlands.Global.AdelicHaarUnimodularityReduction
import Langlands.Global.LocalModularCharacterAdjointDeterminantProof

/-! # Right invariance of Haar measure on actual norm-one adelic groups -/

universe u

namespace Langlands.Global.AdelicGroupPoints

/-- The fixed Haar measure on the actual norm-one adelic subgroup is right
invariant for every smooth connected affine group in the existing statement. -/
theorem normOneHaarRightInvariant :
    NormOneHaarRightInvariantStatement.{u} :=
  normOneHaarRightInvariantStatement_of_local
    PlaceGroupPoints.localModularCharacterAdjointDeterminant.{u}

end Langlands.Global.AdelicGroupPoints
