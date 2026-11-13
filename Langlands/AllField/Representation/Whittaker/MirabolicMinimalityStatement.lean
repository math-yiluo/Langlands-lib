import Langlands.Representation.Whittaker.MirabolicMinimalityStatement
import Langlands.AllField.LocalField.Foundation
/-!
# Compact minimality in the actual mirabolic smooth induction

Bernstein--Zelevinsky (1976), Proposition 5.15(c), printed pp.49--50, for the
mirabolic group over a nonarchimedean local field `F` with supplied data
`T : LocalFieldData F`. This module defines a proposition target; it does not prove it.
-/

namespace Langlands.AllField.Whittaker
open Langlands.Whittaker hiding MirabolicCompactMinimalityStatement
open Langlands.AllField.Whittaker

universe uF

/-- Every nonzero subrepresentation of the standard smooth mirabolic induction
contains its canonical compact-support subrepresentation. The matrix rank is
`n + 1`, including rank one when `n = 0`. -/
def MirabolicCompactMinimalityStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F),
    letI := T.topology
    letI : IsTopologicalRing F := by
      let := T.valuativeRel
      let := T.localField
      infer_instance
    ∀ (n : ℕ) (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F)
      (W : Subrepresentation (mirabolicSmoothInduced ψ n)),
      W ≠ ⊥ → mirabolicCompactSubrepresentation ψ n ≤ W

end Langlands.AllField.Whittaker
