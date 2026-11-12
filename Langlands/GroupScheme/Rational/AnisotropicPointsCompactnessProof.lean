import Langlands.GroupScheme.Rational.SpectralCompactnessPrerequisites
import Langlands.GroupScheme.Rational.ReductiveSpectralBoundednessProof
import Langlands.GroupScheme.Rational.AnisotropicSpectralIntegralityProof

/-! # Compact rational points of anisotropic reductive groups -/

universe u

namespace Langlands.GroupScheme

/-- The exact published proposition, with its structural inputs discharged. -/
theorem anisotropicPointsCompactness :
    AnisotropicPointsCompactnessStatement.{u} :=
  anisotropicPointsCompactness_of_spectral
    reductiveSpectralBoundedness anisotropicSpectralIntegrality

end Langlands.GroupScheme
