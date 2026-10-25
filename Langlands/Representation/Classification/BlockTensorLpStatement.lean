import Langlands.Representation.Classification.BlockTensorAnalyticStatement
import Langlands.Representation.Classification.LpModCenter

/-!
# A common finite-exponent block tensor comparison

This is an internal statement for the common analytic argument behind the
square-integrability and temperedness comparisons. No comparison is proved here.
-/

namespace Langlands

universe uF uV

/-- At every real exponent at least two, the actual external tensor satisfies
the coefficient condition for every Borel Haar realization exactly when every
irreducible admissible factor satisfies the canonical all-Haar condition. -/
def GLBlockTensorLpStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ B : GeneralLinear.BlockShape n,
      letI := T.leviTopology B
      haveI := T.leviTopologicalGroup B
      ∀ (V : Fin B.length → Type uV)
        [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
        (ρ : ∀ i, Representation ℂ (GeneralLinear (B.size i) F.Carrier) (V i)),
        (∀ i, Representation.IsIrreducible (ρ i)) →
        (∀ i, IsAdmissible (ρ i)) →
        ∀ (r : ℝ), 2 ≤ r →
          ((∀ i, T.IsLp (ρ i) r) ↔
            ∀ [MeasurableSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
              [BorelSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
              (μ : MeasureTheory.Measure
                (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)))
              [MeasureTheory.Measure.IsHaarMeasure μ],
              IsLpModCenter (B.blockTensor ρ) μ r)

end Langlands
