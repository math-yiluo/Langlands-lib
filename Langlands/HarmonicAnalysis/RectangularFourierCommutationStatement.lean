import Langlands.HarmonicAnalysis.RectangularFourierEquiv
import Langlands.HarmonicAnalysis.PartialFourierEquiv

/-! Commutation of the chosen full rectangular Fourier equivalence with the chosen
last-column partial Fourier equivalence. -/

namespace Langlands.HarmonicAnalysis

universe uK

/-- For every `n × (n + 1)` Schwartz–Bruhat function, the chosen full plus-sign
Fourier equivalence and the chosen inverse-character last-column Fourier
equivalence commute. This proposition does not supply a proof. -/
def RectangularFourierCommutationStatement : Prop :=
  ∀ {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [MeasurableSpace K] [BorelSpace K]
    [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K) (n : ℕ)
    (hsd : IsSelfDual ψ μ)
    (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)),
    rectangularFourierEquiv ψ μ n (n + 1) hsd (partialFourierEquiv ψ μ n hsd Φ) =
      partialFourierEquiv ψ μ n hsd (rectangularFourierEquiv ψ μ n (n + 1) hsd Φ)

end Langlands.HarmonicAnalysis
