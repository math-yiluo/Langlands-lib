import Langlands.BruhatTits.IntegralModels.UnramifiedTorusConnectedBoundAssembly
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusBoundedModelProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNeutralSurjectivityProof
import Langlands.BruhatTits.IntegralModels.UnramifiedTorusNormPresentationProof

/-! # Integral points of connected torus models lie in the Iwahori subgroup -/

universe u

namespace Langlands.BruhatTits.IntegralModels

/-- **KP Corollary B.8.7 and Proposition B.8.8(3)** over the maximal
unramified field: the integral-point image of every smooth torus model with
geometrically connected fibres lies in the norm-defined Iwahori subgroup. -/
theorem unramifiedTorusConnectedBound :
    UnramifiedTorusConnectedBoundStatement.{u} :=
  unramifiedTorusConnectedBoundAssembly.{u}
    unramifiedTorusBoundedModel.{u}
    unramifiedTorusNeutralSurjectivity.{u}
    unramifiedTorusNormPresentation.{u}

end Langlands.BruhatTits.IntegralModels
