import Langlands.HarmonicAnalysis.Conductor

/-! First-order additive-character coordinates on the actual principal units. -/

namespace Langlands.HarmonicAnalysis

universe u

/-- Killing the quadratic multiplication error makes `psi(c*(u-1))` a continuous
character of p-power order on the actual principal-unit subgroup. -/
def PadicDeepUnitCharacterStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (c : F.Carrier) (n : ℕ),
      T.discreteValuation c * WithZero.exp (-(2 * (n : ℤ))) ≤
          WithZero.exp (T.additiveConductor ψ) →
      ∃ η : T.principalUnits n →ₜ* Circle,
        (∀ z : T.principalUnits n,
          η z = ψ (c * (((z : F.Carrierˣ) : F.Carrier) - 1))) ∧
        ∃ k : ℕ, η ^ (p ^ k) = 1

end Langlands.HarmonicAnalysis
