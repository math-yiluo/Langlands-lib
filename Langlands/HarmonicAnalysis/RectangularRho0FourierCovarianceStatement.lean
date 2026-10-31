import Langlands.HarmonicAnalysis.RectangularFourierEquiv
import Langlands.HarmonicAnalysis.PartialFourierEquiv
import Langlands.Group.GL.Maps
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-! JPSS Section 6.1 formula (7): full Fourier covariance of the transported
action `rectangularRho0` on the `n × (n + 1)` Schwartz space. -/

namespace Langlands.HarmonicAnalysis

universe uK

/-- For every invertible `g` of size `n + 1`, the chosen full rectangular Fourier
equivalence carries the transported action `rectangularRho0` of `g` to the reciprocal
of the `n`-th power of the Haar character of `det g` times the transported action of
the inverse transpose of `g`. This proposition does not supply a proof. -/
def RectangularRho0FourierCovarianceStatement : Prop :=
  ∀ {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [MeasurableSpace K] [BorelSpace K]
    [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K) (n : ℕ)
    (hsd : IsSelfDual ψ μ) (g : Langlands.GeneralLinear (n + 1) K)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)),
    rectangularFourierEquiv ψ μ n (n + 1) hsd (rectangularRho0 ψ μ n hsd g Φ) =
      ((((MeasureTheory.distribHaarChar K
          (Langlands.GeneralLinear.determinant g) : ℝ) : ℂ) ^ n)⁻¹) •
        rectangularRho0 ψ μ n hsd (Langlands.GeneralLinear.inverseTranspose (n + 1) K g)
          (rectangularFourierEquiv ψ μ n (n + 1) hsd Φ)

end Langlands.HarmonicAnalysis
