import Langlands.Geometry.Analytic.Affinoid
import Langlands.Geometry.Analytic.Spectrum.Definitions
import Langlands.Geometry.Analytic.PowerBoundsDefinitions

/-! # The spectral power-bound statement for strict affinoid quotients -/

universe u

namespace Langlands.Analytic.PresentedStrictAffinoidAlgebra

/-- The assigned spectral bound in its full original quotient scope.
This is a proposition definition, not a theorem or an axiom. -/
def SpectralPowerBoundStatement (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : Prop :=
  ∀ (P : PresentedStrictAffinoidAlgebra K) (a : P),
    (∀ x : BanachSpectrum P, x a ≤ 1) → HasBoundedPowers a

end Langlands.Analytic.PresentedStrictAffinoidAlgebra
