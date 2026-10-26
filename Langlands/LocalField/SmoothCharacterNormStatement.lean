import Langlands.LocalField.Normalization.Definitions
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.Group.Units

/-!
# Real norm decomposition of a smooth scalar character

This internal local-field proposition isolates the scalar norm decomposition
motivated by Auel (2004), Lemma 4.15. That source does not state this exact
proposition. This module defines its statement; a proof is a separate obligation.
-/

namespace Langlands.PadicField.TopologicalData

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)

/-- Every complex multiplicative character with open kernel has a unique real
norm exponent for the supplied residue-normalized absolute value. -/
def SmoothCharacterNormDecomposition : Prop :=
  letI := T.topology
  ∀ ω : F.Carrierˣ →* ℂˣ, IsOpen (ω.ker : Set F.Carrierˣ) →
    ∃! c : ℝ, ∀ a : F.Carrierˣ,
      ‖(ω a : ℂ)‖ = T.normalizedAbs (a : F.Carrier) ^ c

end Langlands.PadicField.TopologicalData
