import Langlands.HarmonicAnalysis.Conductor
import Mathlib.Data.Finset.Lattice.Fold

/-!
# Simultaneous additive-character detection after a common prime-power scaling
-/

namespace Langlands.HarmonicAnalysis

universe u

/-- A common sufficiently large inverse power of the rational prime makes a
nontrivial additive character detect every nonzero coefficient in a finite
family on any prescribed actual additive lattice. -/
def PadicFiniteCoefficientSeparationStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (s : Finset F.Carrier) (m : ℤ),
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ a ∈ s,
        (∀ x ∈ T.additiveLattice m,
          ψ.complex (((p : F.Carrier) ^ (-(N : ℤ)) * a) * x) = 1) ↔ a = 0

end Langlands.HarmonicAnalysis
