import Langlands.GroupScheme.IntegralModel.FiniteRecoveryExistence
import Langlands.GroupScheme.IntegralModel.SmoothHomExtensionProof

/-! # Unramified descent of smooth integral group models -/

universe u

namespace Langlands.GroupScheme.IntegralModel

/-- KP Fact 2.10.16 for group-scheme models over nonarchimedean local fields. -/
theorem unramifiedSmoothModelDescent :
    UnramifiedSmoothModelDescentStatement.{u} :=
  unramifiedSmoothModelDescent_of_extension_of_finiteRecovery
    smoothHomExtension finiteUnramifiedRecovery

end Langlands.GroupScheme.IntegralModel
