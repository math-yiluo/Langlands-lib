import Langlands.HarmonicAnalysis.Distribution.GeneralLinear

/-!
# Transpose invariance of conjugation-invariant distributions

This is the unproved distribution theorem used in Bernstein–Zelevinsky
(1976), Section 7.3, specialized to actual p-adic general linear groups.
-/

namespace Langlands

universe uF

/-- Every conjugation-invariant algebraic distribution on a positive-rank
p-adic general linear group is invariant under actual matrix transposition. -/
def GeneralLinearConjugationDistributionTransposeStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalNormedField
    ∀ (n : ℕ)
      (D : HarmonicAnalysis.Distribution
        (Matrix.GeneralLinearGroup (Fin (n + 1)) F.Carrier)),
      HarmonicAnalysis.Distribution.IsConjugationInvariant D →
      HarmonicAnalysis.Distribution.IsTransposeInvariant (n + 1) F.Carrier D

end Langlands
