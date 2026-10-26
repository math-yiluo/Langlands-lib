import Langlands.Representation.Classification.Segments

/-!
# Integral twist freeness of positive-rank cuspidal data

This proposition records nonperiodicity of the actual supercuspidal isomorphism
classes under integral powers of the residue-normalized determinant norm.
-/

namespace Langlands.Classification

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- No nonzero integral real-power determinant twist fixes a positive-rank
cuspidal datum. -/
def CuspidalIntegralTwistFreeness : Prop :=
  ∀ (ρ : T.CuspidalDatum.{uV, uF}) (k : ℤ),
    ρ.twist (k : ℝ) = ρ ↔ k = 0

end Langlands.Classification
