import Langlands.Representation.Classification.TemperedInductionStatement

/-!
# Unitarity of analytically tempered actual block Levi representations

This proposition isolates the input unitarity conclusion of
`GLTemperedInductionStatement`, with exactly the same inputs and hypotheses.
It states the specialization of Silberger's Corollary 4.5.13 to the actual
product Levi; it does not prove that specialization or its analytic comparison.
-/

namespace Langlands

universe uF uV

/-- Every irreducible analytically tempered representation of an actual GL block
Levi admits an invariant positive definite Hermitian form on its given carrier. -/
def GLLeviTemperedUnitarityStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ B : GeneralLinear.BlockShape n,
      let M := B.Levi F.Carrier
      let Q := M ⧸ Subgroup.center M
      ∀ [MeasurableSpace Q] [BorelSpace Q]
        (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ]
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (σ : Representation ℂ M V),
        Representation.IsIrreducible σ → IsTemperedModCenter σ μ →
          IsUnitarizable σ

end Langlands
