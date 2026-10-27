import Langlands.HarmonicAnalysis.Basic
import Langlands.LocalField.Normalization.Definitions

/-!
# Valuation cutoffs and uniform bounds for scalar Schwartz–Bruhat functions

A derived proposition target: on a finite extension of `ℚ_p` with supplied
topological data, every Schwartz–Bruhat function is bounded, vanishes on units
of sufficiently negative order and is constant on units of sufficiently large
order. No proof is supplied here.
-/

namespace Langlands.HarmonicAnalysis

universe uF

/-- Every scalar Schwartz–Bruhat function on a supplied p-adic field has a positive
uniform bound, a lower order cutoff below which it vanishes on units, and an upper
order cutoff above which it equals its value at zero on units. -/
def SchwartzBruhatValuationBoundsStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ Φ : SchwartzBruhat F.Carrier,
      ∃ (L : ℤ) (N : ℕ) (C : ℝ), L ≤ (N : ℤ) ∧ 0 < C ∧
        (∀ x : F.Carrier, ‖Φ x‖ ≤ C) ∧
        (∀ a : F.Carrierˣ, T.ord (a : F.Carrier) < L → Φ (a : F.Carrier) = 0) ∧
        (∀ a : F.Carrierˣ, (N : ℤ) ≤ T.ord (a : F.Carrier) →
          Φ (a : F.Carrier) = Φ 0)

end Langlands.HarmonicAnalysis
