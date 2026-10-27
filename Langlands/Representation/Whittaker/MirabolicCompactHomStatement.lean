import Langlands.Representation.Whittaker.MirabolicModels
import Langlands.LocalField.Canonical

/-!
# Scalar uniqueness of compact-to-smooth mirabolic intertwiners

The p-adic specialization of Bernstein--Zelevinsky (1976), Proposition 5.15(b),
printed p.49, with proof on p.50. This module defines a proposition target; it
does not prove it.
-/

namespace Langlands.Whittaker

universe uF

/-- Every intertwining map from the compactly induced mirabolic model to the
standard smooth mirabolic induction is a complex multiple of the canonical
function inclusion. The matrix rank is `n + 1`, including rank one when
`n = 0`. -/
def MirabolicCompactHomScalarStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    letI : IsTopologicalRing F.Carrier := by
      let := F.canonicalTopologicalData.valuativeRel
      let := F.canonicalTopologicalData.localField
      infer_instance
    ∀ (n : ℕ) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
      (A : (mirabolicCompactInduced ψ n).IntertwiningMap (mirabolicSmoothInduced ψ n)),
      ∃ c : ℂ, A = c • mirabolicCompactInclusion ψ n

end Langlands.Whittaker
