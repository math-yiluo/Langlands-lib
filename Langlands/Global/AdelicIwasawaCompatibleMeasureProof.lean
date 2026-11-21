import Langlands.Global.AdelicIwasawaCompatibleMeasureReduction
import Langlands.Global.AdelicIwasawaIntegrationProof
import Langlands.Global.AdelicParabolicModulusProof

/-! # Existence of an Iwasawa-compatible Haar measure on the Levi -/

set_option autoImplicit false

namespace Langlands.Global

/-- The Iwasawa integration formula and the parabolic modulus theorem supply the two
inputs of the Haar-normalization reduction. -/
theorem iwasawaCompatibleMeasureExistence : IwasawaCompatibleMeasureExistenceStatement :=
  iwasawaCompatibleMeasureIntegrationReduction AdelicGroupPoints.adelicIwasawaIntegration
    AdelicGroupPoints.adelicParabolicModulus

end Langlands.Global
