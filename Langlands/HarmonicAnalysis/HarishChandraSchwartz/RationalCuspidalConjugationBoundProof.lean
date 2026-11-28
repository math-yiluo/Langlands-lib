import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCuspidalConjugationAssembly
import Langlands.BruhatTits.SpecialCompact.JointBasisProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiUpperBoundProof
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalConstantTermEstimateProof

/-! # Waldspurger VIII.3.1 for the actual intrinsic cuspidal Schwartz kernel -/

universe u

namespace Langlands.HarishChandraSchwartz

/-- Waldspurger's Proposition VIII.3.1 on actual rational points: for every
intrinsic cuspidal Schwartz function `f₁`, every Schwartz function `f₂` and every
conjugator `h`, the function `g ↦ f₁(h g h⁻¹) f₂(g)` is integrable for the given
Haar measure, and for every real `r` the conjugation integral is bounded by a
constant times `δ₀(a) (1 + σ(a))^(-r)` on the minimal chamber in the common norm
kernel `G¹`. -/
theorem rationalCuspidalConjugationBound : RationalCuspidalConjugationBoundStatement.{u} :=
  rationalCuspidalConjugationBound_of_prerequisites.{u}
    ⟨Langlands.BruhatTits.SpecialCompact.jointSpecialCompactBasisExistence.{u},
      rationalXiUpperBound.{u}, rationalConstantTermEstimate.{u}⟩

end Langlands.HarishChandraSchwartz
