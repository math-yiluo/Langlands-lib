import Langlands.HarmonicAnalysis.RectangularFourierEquiv
import Langlands.Group.GL.Maps
import Mathlib.MeasureTheory.Measure.Haar.DistribChar

/-! Covariance of the chosen full rectangular Fourier equivalence under the right
action of the general linear group. -/

namespace Langlands.HarmonicAnalysis

universe uK

/-- For every invertible `g`, the chosen full rectangular Fourier equivalence carries
right translation by `g` to the reciprocal of the `r`-th power of the Haar character
of `det g` times right translation by the inverse transpose of `g`.
This proposition does not supply a proof. -/
def RectangularFourierCovarianceStatement : Prop :=
  ∀ {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [MeasurableSpace K] [BorelSpace K]
    [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K) (r s : ℕ)
    (hsd : IsSelfDual ψ μ) (g : Langlands.GeneralLinear s K)
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K)),
    rectangularFourierEquiv ψ μ r s hsd (rectangularTranslate g Φ) =
      ((((MeasureTheory.distribHaarChar K
          (Langlands.GeneralLinear.determinant g) : ℝ) : ℂ) ^ r)⁻¹) •
        rectangularTranslate (Langlands.GeneralLinear.inverseTranspose s K g)
          (rectangularFourierEquiv ψ μ r s hsd Φ)

end Langlands.HarmonicAnalysis
