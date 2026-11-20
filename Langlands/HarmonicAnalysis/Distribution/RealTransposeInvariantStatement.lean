import Langlands.HarmonicAnalysis.Distribution.RealGeneralLinear

/-! # Transposition of conjugation-invariant real general linear distributions -/

namespace Langlands

/-- Aizenbud–Gourevitch, Corollary 7.6.3, for `GL_(r+1)(ℝ)`. Every conjugation-invariant
complex-valued distribution is invariant under actual ordinary matrix transpose. -/
def RealGeneralLinearConjugationDistributionTransposeStatement : Prop :=
  ∀ (r : ℕ) (D : HarmonicAnalysis.RealGeneralLinearDistribution.Distribution (r + 1)),
    HarmonicAnalysis.RealGeneralLinearDistribution.IsConjugationInvariant D →
    HarmonicAnalysis.RealGeneralLinearDistribution.IsTransposeInvariant D

end Langlands
