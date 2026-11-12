import Langlands.Global.AdelicNormOneHaarRightInvariantProof
import Langlands.GroupScheme.Reductive.CentralDerivedProductReduction
import Langlands.GroupScheme.Reductive.CentralTorusSurjectivityProof

/-! # Haar unimodularity of actual norm-one and connected reductive adelic groups -/

universe u

namespace Langlands.Global.AdelicGroupPoints

/-- The fixed Haar measures on the actual norm-one subgroup of every smooth
connected affine group, and on the full actual adelic points of every connected
reductive group, over every number field, are right invariant. -/
theorem adelicHaarUnimodularity :
    AdelicHaarUnimodularityStatement.{u} :=
  adelicHaarUnimodularityStatement_of_local_and_centralDerivedProduct
    PlaceGroupPoints.localModularCharacterAdjointDeterminant.{u}
    (Langlands.GroupScheme.reductiveCentralDerivedProduct_of_torusSurjectivity
      Langlands.GroupScheme.reductiveCentralTorusSurjectivity.{u})

end Langlands.Global.AdelicGroupPoints
