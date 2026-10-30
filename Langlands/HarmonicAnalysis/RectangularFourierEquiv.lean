import Langlands.HarmonicAnalysis.RectangularFourierCompatibilityProof

/-! The chosen full rectangular Schwartz Fourier equivalence and its evaluation API. -/

noncomputable section

open MeasureTheory

namespace Langlands.HarmonicAnalysis

universe uK

variable {K : Type uK} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
  [MeasurableSpace K] [BorelSpace K]
  [LocallyCompactSpace K] [T2Space K] [TotallyDisconnectedSpace K]
  (ψ : UnitaryAdditiveCharacter K) (μ : AdditiveHaarMeasure K) (r s : ℕ)
  (hsd : IsSelfDual ψ μ)

/-- The chosen witness of the published full rectangular Fourier theorem: a
complex-linear equivalence of the rectangular Schwartz space realizing the
plus-sign Fourier integral against the supplied nested product measure. -/
def rectangularFourierEquiv :
    SchwartzBruhat (Matrix (Fin r) (Fin s) K) ≃ₗ[ℂ]
      SchwartzBruhat (Matrix (Fin r) (Fin s) K) :=
  Classical.choose (rectangularFourierCompatibility.{uK} ψ μ r s hsd)

/-- Forward evaluation: the chosen equivalence is the plus-sign Fourier integral. -/
theorem rectangularFourierEquiv_apply
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K)) (b : Matrix (Fin r) (Fin s) K) :
    rectangularFourierEquiv ψ μ r s hsd Φ b = rectangularFourierIntegral ψ μ Φ b :=
  (Classical.choose_spec (rectangularFourierCompatibility.{uK} ψ μ r s hsd)).1 Φ b

/-- Inverse evaluation: the inverse is the same plus-sign integral at `-b`. -/
theorem rectangularFourierEquiv_symm_apply
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K)) (b : Matrix (Fin r) (Fin s) K) :
    (rectangularFourierEquiv ψ μ r s hsd).symm Φ b =
      rectangularFourierIntegral ψ μ Φ (-b) :=
  (Classical.choose_spec (rectangularFourierCompatibility.{uK} ψ μ r s hsd)).2.1 Φ b

/-- Square-reflection: applying the chosen equivalence twice evaluates to `Φ (-b)`. -/
theorem rectangularFourierEquiv_apply_apply
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K)) (b : Matrix (Fin r) (Fin s) K) :
    rectangularFourierEquiv ψ μ r s hsd (rectangularFourierEquiv ψ μ r s hsd Φ) b =
      Φ (-b) :=
  (Classical.choose_spec (rectangularFourierCompatibility.{uK} ψ μ r s hsd)).2.2.1 Φ b

include hsd in
/-- Convergence: under scalar self-duality every full Fourier integrand of a
rectangular Schwartz function is integrable against the supplied nested product
measure. -/
theorem rectangularFourierEquiv_integrable
    (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K)) (b : Matrix (Fin r) (Fin s) K) :
    Integrable (fun a => Φ a * ψ.complex (rectangularPairing a b))
      (RankinSelberg.rectangularMeasure μ r s) :=
  (Classical.choose_spec (rectangularFourierCompatibility.{uK} ψ μ r s hsd)).2.2.2 Φ b

/-- Any complex-linear equivalence of the same Schwartz space with the forward
plus-sign Fourier evaluation is the chosen equivalence. -/
theorem rectangularFourierEquiv_unique
    (T : SchwartzBruhat (Matrix (Fin r) (Fin s) K) ≃ₗ[ℂ]
      SchwartzBruhat (Matrix (Fin r) (Fin s) K))
    (hT : ∀ (Φ : SchwartzBruhat (Matrix (Fin r) (Fin s) K))
      (b : Matrix (Fin r) (Fin s) K), T Φ b = rectangularFourierIntegral ψ μ Φ b) :
    T = rectangularFourierEquiv ψ μ r s hsd :=
  LinearEquiv.ext fun Φ => Hecke.TestFunction.ext fun b =>
    (hT Φ b).trans (rectangularFourierEquiv_apply ψ μ r s hsd Φ b).symm

end Langlands.HarmonicAnalysis
