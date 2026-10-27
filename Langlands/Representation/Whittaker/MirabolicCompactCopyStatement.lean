import Langlands.Representation.Whittaker.MirabolicModels
import Langlands.LocalField.Canonical

/-!
# Nonzero compact standard maps into actual mirabolic subrepresentations

The existential compact-copy input in the proof of Bernstein--Zelevinsky (1976),
Proposition 5.15(c), printed pp.49--50, specialized to p-adic fields. This module
defines a proposition target; it does not prove it.
-/

namespace Langlands.Whittaker

universe uF

/-- Every nonzero subrepresentation of the standard smooth mirabolic induction
receives a nonzero intertwining map from the compact standard induction.
The matrix rank is `n + 1`, including rank one when `n = 0`. -/
def MirabolicNonzeroCompactMapStatement : Prop :=
  ∀ (p : ℕ) (_hp : Fact p.Prime) (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    letI : IsTopologicalRing F.Carrier := by
      let := F.canonicalTopologicalData.valuativeRel
      let := F.canonicalTopologicalData.localField
      infer_instance
    ∀ (n : ℕ) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
      (W : Subrepresentation (mirabolicSmoothInduced ψ n)),
      W ≠ ⊥ →
        ∃ A : (mirabolicCompactInduced ψ n).IntertwiningMap W.toRepresentation,
          A ≠ 0

end Langlands.Whittaker
