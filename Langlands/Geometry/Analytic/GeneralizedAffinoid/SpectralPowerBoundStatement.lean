import Langlands.Geometry.Analytic.GeneralizedAffinoid.Definitions
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Banach
import Langlands.Geometry.Analytic.Spectrum.Definitions
import Langlands.Geometry.Analytic.WeightedPowerBounds

/-! # The arbitrary-radius spectral power statement for affinoid quotients -/

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

/-- Pointwise spectral bounds at a positive radius give radius-weighted bounded
powers in every actual finite positive-polyradius quotient presentation.
This is a proposition definition, not a theorem or an axiom. -/
def SpectralPowerBoundStatement (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : Prop :=
  ∀ (P : PresentedAffinoidAlgebra K) (a : P) (r : ℝ), 0 < r →
    (∀ x : BanachSpectrum P, x a ≤ r) → HasRadiusBoundedPowers r a

end Langlands.Analytic.PresentedAffinoidAlgebra
