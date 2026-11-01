import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.RankinSelberg.SpectralRescaling
import Langlands.Representation.Twist.Definitions

noncomputable section

namespace Langlands.RankinSelberg

open HarmonicAnalysis GeneralLinear

universe uF uV uW

/-- Twisting either member by the supplied determinant power shifts the complete
symmetric rational gamma factor by the actual spectral substitution. -/
def UnramifiedTwistGammaStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    (r t : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]
    {W : Type uW} [AddCommGroup W] [Module ℂ W]
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W)
    (u : ℂ) (χ : F.Carrierˣ →* ℂˣ),
    (∀ x : F.Carrierˣ,
      (χ x : ℂ) = ((F.canonicalTopologicalData.normalizedAbs (x : F.Carrier) : ℝ) : ℂ) ^ u) →
    ∀ G : RationalFunctions, IsPadicSymmetricGammaFactor F ψ ν.val π σ G →
      IsPadicSymmetricGammaFactor F ψ ν.val π (Langlands.twist (χ.comp determinant) σ)
        (rationalRescale (spectralShiftUnit F.canonicalTopologicalData.residueCardinality
          F.canonicalTopologicalData.residueCardinality_gt_one u) G) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val (Langlands.twist (χ.comp determinant) π) σ
        (rationalRescale (spectralShiftUnit F.canonicalTopologicalData.residueCardinality
          F.canonicalTopologicalData.residueCardinality_gt_one u) G)

end Langlands.RankinSelberg
