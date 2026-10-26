import Langlands.Representation.Classification.Tempered

/-!
# Elementary central-character reductions for square-integrability

These reductions retain the actual central quotient and every Borel Haar measure.
They contain no assertion about Jacquet exponents or coefficient integrability.
-/

namespace Langlands

universe uF uV

/-- For a nonzero admissible scalar-character representation, the scalar
character has open kernel, a unitary character of the actual centre exists
exactly when the scalar character is unitary, and square-integrability can be
tested using any fixed such datum for every Haar measure. -/
def GLSquareIntegrableCentralCharacterStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    (n : ℕ), 0 < n →
    ∀ (V : Type uV) [AddCommGroup V] [Module ℂ V] [Nontrivial V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V)
      (ω : F.Carrierˣ →* ℂˣ),
      (letI := T.topology; IsAdmissible ρ) →
      (∀ a v, ρ (GeneralLinear.scalar a) v = (ω a : ℂ) • v) →
      letI := T.topology
      haveI := T.generalLinearTopologicalGroup n
      letI := T.centralQuotientMeasurableSpace n
      haveI := T.centralQuotientBorelSpace n
      IsOpen (ω.ker : Set F.Carrierˣ) ∧
      (Nonempty (UnitaryCentralCharacter ρ) ↔ ∀ a, ‖(ω a : ℂ)‖ = 1) ∧
      (T.IsSquareIntegrable ρ → ∀ a, ‖(ω a : ℂ)‖ = 1) ∧
      (∀ c : UnitaryCentralCharacter ρ,
        T.IsSquareIntegrable ρ ↔
          ∀ (μ : MeasureTheory.Measure
            (GeneralLinear n F.Carrier ⧸ Subgroup.center (GeneralLinear n F.Carrier)))
            [MeasureTheory.Measure.IsHaarMeasure μ]
            (ℓ : SmoothDual ρ) (v : V),
            MeasureTheory.MemLp (c.coefficientNorm ℓ v) 2 μ)

end Langlands
