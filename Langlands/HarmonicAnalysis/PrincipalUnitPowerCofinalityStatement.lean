import Langlands.HarmonicAnalysis.Conductor

/-!
# Principal-unit powers and uniform conductor bounds

This is a derived local-field prerequisite for high-ramification arguments.
It uses the existing valuation filtration and conductor without changing them.
The proposition is stated here; its proof is a separate obligation.
-/

namespace Langlands.HarmonicAnalysis

universe uF

/-- Every fixed positive power of the actual principal units contains a deep
unit subgroup, and characters of sufficiently large conductor have that power
nontrivial on the prescribed unit subgroup. The bound precedes the character. -/
def PrincipalUnitPowerCofinalityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    letI := T.valuativeRel
    letI := T.localField
    ∀ (b m : ℕ), 0 < m →
      (∃ N : ℕ, ∀ u : F.Carrierˣ, u ∈ T.principalUnits N →
        ∃ v : F.Carrierˣ, v ∈ T.principalUnits b ∧ v ^ m = u) ∧
      (∃ A : ℕ, ∀ χ : Quasicharacter F.Carrier,
        A ≤ T.multiplicativeConductor χ →
        ∃ v : F.Carrierˣ, v ∈ T.principalUnits b ∧ (χ v) ^ m ≠ 1)

end Langlands.HarmonicAnalysis
