import Langlands.HarmonicAnalysis.RectangularFourier

/-! The last-column partial Fourier transform as an actual equivalence of
rectangular Schwartz spaces, with convergence of both partial integrals. -/

namespace Langlands.HarmonicAnalysis

/-- From scalar self-duality, the inverse-character last-column partial Fourier
integral on `n × (n + 1)` matrices is an actual complex-linear equivalence of
Schwartz–Bruhat spaces whose inverse is the plus-character companion, and both
partial integrands converge on every Schwartz input. This proposition does not
supply a proof. -/
def PartialFourierCompatibilityStatement.{uK} : Prop :=
  ∀ {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [MeasurableSpace K] [BorelSpace K]
    [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
    (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K) (n : ℕ),
    IsSelfDual ψ μ →
      ∃ T : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K) ≃ₗ[ℂ]
          SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K),
        (∀ (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
            (m : Matrix (Fin n) (Fin (n + 1)) K),
          T Φ m = partialFourierIntegral ψ μ Φ m) ∧
        (∀ (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
            (m : Matrix (Fin n) (Fin (n + 1)) K),
          T.symm Φ m = partialFourierPlusIntegral ψ μ Φ m) ∧
        (∀ (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
            (m : Matrix (Fin n) (Fin (n + 1)) K),
          MeasureTheory.Integrable
            (fun u => Φ (rectangularJoin (rectangularFirstColumns m) u) *
              ψ.complex (-rowPairing (rectangularLastColumn m) u))
            (rowMeasure μ n)) ∧
        ∀ (Φ : SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K))
            (m : Matrix (Fin n) (Fin (n + 1)) K),
          MeasureTheory.Integrable
            (fun u => Φ (rectangularJoin (rectangularFirstColumns m) u) *
              ψ.complex (rowPairing (rectangularLastColumn m) u))
            (rowMeasure μ n)

end Langlands.HarmonicAnalysis
