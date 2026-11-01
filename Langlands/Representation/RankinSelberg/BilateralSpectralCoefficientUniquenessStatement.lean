import Langlands.HarmonicAnalysis.BilateralLaurentSeries
import Langlands.Representation.RankinSelberg.RationalContinuation

/-!
# Uniqueness of absolutely convergent bilateral spectral coefficients

This is a derived scalar analytic prerequisite for passing from equality of
convergent spectral sums to equality of the original bilateral coefficients.
The proposition is stated here; its proof is a separate obligation.
-/

namespace Langlands.RankinSelberg

/-- Two unrestricted bilateral coefficient series are equal if their actual
spectral sums converge absolutely and agree throughout a right half-plane. -/
def BilateralSpectralCoefficientUniquenessStatement : Prop :=
  ∀ (q : ℕ), 1 < q →
    ∀ (a b : Langlands.HarmonicAnalysis.BilateralLaurentSeries),
      (∃ C : ℝ, ∀ s : ℂ, C < s.re →
        Summable (fun m : ℤ => ‖a m * spectralPoint q s ^ m‖) ∧
        Summable (fun m : ℤ => ‖b m * spectralPoint q s ^ m‖) ∧
        (∑' m : ℤ, a m * spectralPoint q s ^ m) =
          (∑' m : ℤ, b m * spectralPoint q s ^ m)) →
      a = b

end Langlands.RankinSelberg
