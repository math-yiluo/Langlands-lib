import Langlands.HarmonicAnalysis.RectangularFourier

/-! Full rectangular Fourier equivalence and reflection from scalar self-duality. -/

open MeasureTheory

namespace Langlands.HarmonicAnalysis

universe uK

/-- Scalar self-duality gives an actual Schwartz linear equivalence realizing the
plus-sign full rectangular Fourier integral, with the reflected inverse formula,
Fourier squared equal to reflection, and convergence of every Fourier integrand.
This proposition does not supply a proof. -/
def RectangularFourierCompatibilityStatement : Prop :=
  ∀ {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [MeasurableSpace K] [BorelSpace K]
    [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K) (r s : ℕ),
    IsSelfDual ψ μ →
      ∃ T : SchwartzBruhat (Matrix (Fin r) (Fin s) K) ≃ₗ[ℂ]
          SchwartzBruhat (Matrix (Fin r) (Fin s) K),
        (∀ (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K))
            (b : Matrix (Fin r) (Fin s) K),
          T Φ b = rectangularFourierIntegral ψ μ Φ b) ∧
        (∀ (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K))
            (b : Matrix (Fin r) (Fin s) K),
          T.symm Φ b = rectangularFourierIntegral ψ μ Φ (-b)) ∧
        (∀ (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K))
            (b : Matrix (Fin r) (Fin s) K),
          T (T Φ) b = Φ (-b)) ∧
        ∀ (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K))
            (b : Matrix (Fin r) (Fin s) K),
          Integrable (fun a => Φ a * ψ.complex (rectangularPairing a b))
            (RankinSelberg.rectangularMeasure μ r s)

end Langlands.HarmonicAnalysis
