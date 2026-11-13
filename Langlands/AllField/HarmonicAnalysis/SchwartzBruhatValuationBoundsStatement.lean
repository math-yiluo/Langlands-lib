import Langlands.HarmonicAnalysis.SchwartzBruhatValuationBoundsStatement
import Langlands.AllField.LocalField.Foundation
/-!
# Valuation cutoffs and uniform bounds for scalar Schwartz–Bruhat functions

A derived proposition target: on a nonarchimedean local field with supplied
topological data, every Schwartz–Bruhat function is bounded, vanishes on units
of sufficiently negative order and is constant on units of sufficiently large
order. No proof is supplied here.
-/

namespace Langlands.AllField.HarmonicAnalysis
open Langlands.HarmonicAnalysis hiding SchwartzBruhatValuationBoundsStatement
open Langlands.AllField.HarmonicAnalysis

universe uF

/-- Every scalar Schwartz–Bruhat function on a supplied nonarchimedean local field has a positive
uniform bound, a lower order cutoff below which it vanishes on units, and an upper
order cutoff above which it equals its value at zero on units. -/
def SchwartzBruhatValuationBoundsStatement : Prop :=
  ∀ (F : Type uF) [Field F] (T : LocalFieldData F),
    letI := T.topology
    ∀ Φ : SchwartzBruhat F,
      ∃ (L : ℤ) (N : ℕ) (C : ℝ), L ≤ (N : ℤ) ∧ 0 < C ∧
        (∀ x : F, ‖Φ x‖ ≤ C) ∧
        (∀ a : Fˣ, T.ord (a : F) < L → Φ (a : F) = 0) ∧
        (∀ a : Fˣ, (N : ℤ) ≤ T.ord (a : F) →
          Φ (a : F) = Φ 0)

end Langlands.AllField.HarmonicAnalysis
