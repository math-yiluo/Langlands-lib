import Langlands.HarmonicAnalysis.Conductor

/-!
# Canonical norm depth and character conductors

These proposition definitions compare the base-extending canonical norm
with the actual principal-unit filtration and multiplicative conductor.
They make no character-existence assertion.
-/

noncomputable section

universe u

namespace Langlands.HarmonicAnalysis

/-- Every prescribed principal-unit level contains a sufficiently small
canonical norm ball about one, uniformly in the character. -/
def CanonicalPrincipalUnitDepthStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p)
    (T : F.TopologicalData) (n : ℕ),
    ∃ s : ℕ, ∀ x : F.Carrierˣ,
      F.canonicalNorm ((x : F.Carrier) - 1) < (p : ℝ) ^ (-(s : ℤ)) →
      x ∈ T.principalUnits n

/-- For any additional character property, arbitrarily deep nontriviality
in the canonical norm is equivalent to unbounded multiplicative conductor.
The same property is retained on both sides. -/
def CanonicalCharacterDepthStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ P : (F.Carrierˣ →ₜ* ℂˣ) → Prop,
      (∀ s : ℕ, ∃ χ : F.Carrierˣ →ₜ* ℂˣ, P χ ∧
        ∃ x : F.Carrierˣ,
          F.canonicalNorm ((x : F.Carrier) - 1) < (p : ℝ) ^ (-(s : ℤ)) ∧ χ x ≠ 1) ↔
      (∀ r : ℕ, ∃ χ : F.Carrierˣ →ₜ* ℂˣ,
        P χ ∧ r ≤ T.multiplicativeConductor χ)

/-- The two comparisons used to convert auxiliary-character depth to
the Library conductor convention. -/
def CanonicalConductorDepthStatement : Prop :=
  CanonicalPrincipalUnitDepthStatement.{u} ∧ CanonicalCharacterDepthStatement.{u}

end Langlands.HarmonicAnalysis
