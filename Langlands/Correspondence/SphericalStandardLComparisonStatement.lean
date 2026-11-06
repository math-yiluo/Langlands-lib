import Langlands.Correspondence.FullLFactorCompatibility
import Langlands.Representation.Unramified.PrincipalSeries

/-!
# The standard L-polynomial on spherical classes

This internal comparison obligation identifies a supplied Langlands-defined
standard L-polynomial with the Euler polynomial of the spherical spectrum.
It includes spherical representations without a genericity or unitarity
hypothesis and does not assert that the obligation has been proved.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- On a spherical class, a supplied Langlands-defined L-polynomial against the
trivial rank-one class is the Euler polynomial of its spherical spectrum.
The additive character is arbitrary and the measure is self-dual. -/
def SphericalStandardLComparisonStatement : Prop :=
  ∀ (ψ : NontrivialAdditiveCharacter F) (ν : LocalAdditiveHaarMeasure F),
    IsSelfDualMeasure F ψ ν →
      ∀ (r : ℕ) (π : AutomorphicClass.{uF, uA} F r.succPNat)
        (π0 : AutomorphicClass.{uF, uA} F 1)
        (s : Unramified.Eigenvalues (r + 1)) (P : Polynomial ℂ),
        IsRankOneCharacter F 1 π0 →
        Unramified.HasSphericalSpectrumClass F π s →
        IsAutomorphicPairLPolynomial F ψ ν π π0 P →
        P = Unramified.Eigenvalues.eulerPolynomial s

end Langlands.Correspondence
