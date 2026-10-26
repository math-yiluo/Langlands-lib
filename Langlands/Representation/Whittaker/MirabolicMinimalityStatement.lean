import Langlands.Representation.Whittaker.MirabolicModels
import Langlands.LocalField.Canonical

/-!
# Compact minimality in the actual mirabolic smooth induction

The p-adic specialization of Bernstein--Zelevinsky (1976), Proposition 5.15(c),
printed pp.49--50. This module defines a proposition target; it does not prove it.
-/

namespace Langlands.Whittaker

universe uF

/-- Every nonzero subrepresentation of the standard smooth mirabolic induction
contains its canonical compact-support subrepresentation. The matrix rank is
`n + 1`, including rank one when `n = 0`. -/
def MirabolicCompactMinimalityStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    letI : IsTopologicalRing F.Carrier := by
      let := F.canonicalTopologicalData.valuativeRel
      let := F.canonicalTopologicalData.localField
      infer_instance
    ∀ (n : ℕ) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
      (W : Subrepresentation (mirabolicSmoothInduced ψ n)),
      W ≠ ⊥ → mirabolicCompactSubrepresentation ψ n ≤ W

end Langlands.Whittaker
