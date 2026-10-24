import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Induction.BlockFactors

/-!
# Analytic properties of actual block tensors

The external tensor of irreducible admissible GL block representations is
tempered, respectively square-integrable, modulo the actual product Levi center
exactly when every factor has that analytic property. These are statements;
the analytic product comparisons are not proved here.
-/

namespace Langlands

universe uF uV

/-- Analytic temperedness of every irreducible admissible block factor is
equivalent to analytic temperedness of their actual tensor for every Borel Haar
measure on the actual Levi central quotient. -/
def GLBlockTensorTemperedStatement : Prop :=
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
          ((∀ i, T.IsTempered (ρ i)) ↔
            ∀ [MeasurableSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
              [BorelSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
              (μ : MeasureTheory.Measure
                (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)))
              [MeasureTheory.Measure.IsHaarMeasure μ],
              IsTemperedModCenter (B.blockTensor ρ) μ)

/-- Analytic square-integrability of every irreducible admissible block factor
is equivalent to analytic square-integrability of their actual tensor for every
Borel Haar measure on the actual Levi central quotient. -/
def GLBlockTensorSquareIntegrableStatement : Prop :=
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
          ((∀ i, T.IsSquareIntegrable (ρ i)) ↔
            ∀ [MeasurableSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
              [BorelSpace (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier))]
              (μ : MeasureTheory.Measure
                (B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)))
              [MeasureTheory.Measure.IsHaarMeasure μ],
              IsSquareIntegrableModCenter (B.blockTensor ρ) μ)

/-- Both analytic comparisons for actual irreducible admissible GL block tensors. -/
def GLBlockTensorAnalyticStatement : Prop :=
  GLBlockTensorTemperedStatement.{uF, uV} ∧
    GLBlockTensorSquareIntegrableStatement.{uF, uV}

end Langlands
