import Langlands.HarmonicAnalysis.Conductor
import Mathlib.RingTheory.Norm.Defs
import Mathlib.RingTheory.Trace.Defs

/-! First-order character coordinates commute with actual finite field norms. -/

namespace Langlands.HarmonicAnalysis

universe u v

/-- On sufficiently deep actual units, the norm pullback of a prescribed
first-order character is the additive trace formula. -/
def PadicDeepUnitNormTraceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [FiniteDimensional F.Carrier E.Carrier]
    (T : F.TopologicalData) (S : E.TopologicalData),
    letI := T.topology
    ∀ (ψ : UnitaryAdditiveCharacter F.Carrier) (c : F.Carrier) (n : ℕ)
      (χ : F.Carrierˣ →ₜ* ℂˣ),
      (∀ z : T.principalUnits n,
        χ (z : F.Carrierˣ) = Circle.toUnits (ψ (c * (((z : F.Carrierˣ) : F.Carrier) - 1)))) →
      ∀ (a : T.Integers),
        T.discreteValuation (a : F.Carrier) < 1 →
        T.discreteValuation (a : F.Carrier) ≤ WithZero.exp (-(n : ℤ)) →
        T.discreteValuation c * T.discreteValuation (a : F.Carrier) ^ 2 ≤
          WithZero.exp (T.additiveConductor ψ) →
        ∀ y : S.Integers, ∃ z : E.Carrierˣ,
          (z : E.Carrier) =
            1 + algebraMap F.Carrier E.Carrier (a : F.Carrier) * (y : E.Carrier) ∧
          Units.map (Algebra.norm F.Carrier) z ∈ T.principalUnits n ∧
          χ (Units.map (Algebra.norm F.Carrier) z) =
            Circle.toUnits (ψ (c * (a : F.Carrier) *
              Algebra.trace F.Carrier E.Carrier (y : E.Carrier)))

end Langlands.HarmonicAnalysis
