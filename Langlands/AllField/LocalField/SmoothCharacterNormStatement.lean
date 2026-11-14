import Langlands.LocalField.SmoothCharacterNormStatement
import Langlands.AllField.LocalField.Foundation
/-!
# Real norm decomposition of a smooth scalar character

This internal local-field proposition isolates the scalar norm decomposition
motivated by Auel (2004), Lemma 4.15. That source does not state this exact
proposition. This module defines its statement; a proof is a separate obligation.
-/

namespace Langlands.LocalFieldData
open Langlands.LocalFieldData

universe uF

variable (F : Type uF) [Field F] (T : LocalFieldData F)

/-- Every complex multiplicative character with open kernel has a unique real
norm exponent for the supplied residue-normalized absolute value. -/
def SmoothCharacterNormDecomposition : Prop :=
  letI := T.topology
  ∀ ω : Fˣ →* ℂˣ, IsOpen (ω.ker : Set Fˣ) →
    ∃! c : ℝ, ∀ a : Fˣ,
      ‖(ω a : ℂ)‖ = T.normalizedAbs (a : F) ^ c

end Langlands.LocalFieldData
