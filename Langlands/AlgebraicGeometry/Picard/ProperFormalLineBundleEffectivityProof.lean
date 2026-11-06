import Langlands.AlgebraicGeometry.Modules.ProperFormalCoherentExistenceProof
import Langlands.AlgebraicGeometry.Picard.ProperFormalLineBundleEffectivityReduction

/-! # Proper formal line-bundle effectivity over complete local rings -/

universe u

namespace Langlands.AlgebraicGeometry.Picard

/-- Every compatible system of actual line bundles on the maximal-ideal
thickenings of a proper scheme over a complete local noetherian ring has an
actual line-bundle algebraization compatible with every transition. -/
theorem properFormalLineBundleEffectivity : ProperFormalLineBundleEffectivityStatement.{u} :=
  properFormalLineBundleEffectivity_of_coherentExistence
    Modules.properFormalCoherentExistence

end Langlands.AlgebraicGeometry.Picard
