import Langlands.BruhatTits.IntegralModels.UnramifiedNearbyParabolicComparisons
import Langlands.BruhatTits.IntegralModels.IntegralOppositeFactorsProof

/-! # Proof of depth-zero opposite factors at the Galois-fixed points -/

universe u

namespace Langlands.Geometry.Building

/-- **KP Proposition 9.4.9(2)**, restricted form: at every `Aut(K/F)`-fixed point
of the unramified apartment, a nontrivial depth-zero root point has opposite
factors of nonnegative restricted value. -/
theorem unramifiedFixedDepthZeroOpposite :
    UnramifiedFixedDepthZeroOppositeStatement.{u} :=
  unramifiedFixedDepthZeroOpposite_of_recoveredParabolicModels
    unramifiedFixedRecoveredParabolicModels
    Langlands.BruhatTits.IntegralModels.integralOppositeFactors

end Langlands.Geometry.Building
