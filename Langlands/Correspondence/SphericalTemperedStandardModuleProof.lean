import Langlands.Correspondence.SphericalStandardModuleReduction
import Langlands.Correspondence.OrderedUnramifiedSphericalGenerationProof
import Langlands.Correspondence.OrderedUnramifiedTemperedRealizationProof

/-! # Ordered unramified standard modules for spherical representations -/

namespace Langlands.Correspondence

universe uF uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Every spherical representation has a tempered quotient presentation whose
actual standard module is an ordered unramified principal series with the
prescribed spherical spectrum. -/
theorem sphericalTemperedStandardModule :
    SphericalTemperedStandardModuleStatement.{uF, uA} F :=
  sphericalTemperedStandardModule_of_prerequisites.{uF, uA} F
    (orderedUnramifiedSphericalGeneration.{uF} F)
    (orderedUnramifiedTemperedRealization.{uF, uA} F)

end Langlands.Correspondence
