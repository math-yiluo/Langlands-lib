import Langlands.Representation.Classification.RelativeRegularComparisonStatement

/-! # Fixed-Haar tests for analytic temperedness on actual GL groups and Levis -/

namespace Langlands

universe uF uV

/-- The universal-Haar GL predicate is equivalent to its test at any one Haar
measure in any Borel measurable-space realization of the full central quotient. -/
def GLTemperedFixedHaarStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ),
      let G := GeneralLinear n F.Carrier
      let Q := G ⧸ Subgroup.center G
      ∀ [MeasurableSpace Q] [BorelSpace Q]
        (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ]
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (ρ : Representation ℂ G V),
        T.IsTempered ρ ↔ IsTemperedModCenter ρ μ

/-- Temperedness for one supplied Borel Haar measure on an actual product Levi
extends to every Borel realization and every Haar measure of its full central
quotient, with the representation and topology fixed. -/
def GLLeviTemperedHaarExtensionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ) (B : GeneralLinear.BlockShape n),
      let M := B.Levi F.Carrier
      let Q := M ⧸ Subgroup.center M
      ∀ [MeasurableSpace Q] [BorelSpace Q]
        (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ]
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (σ : Representation ℂ M V),
        IsTemperedModCenter σ μ →
          ∀ [MeasurableSpace Q] [BorelSpace Q]
            (ν : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure ν],
            IsTemperedModCenter σ ν

/-- The ambient GL fixed-Haar criterion and the cross-Borel actual-Levi
extension, with independent field and representation-carrier universes. -/
def GLTemperedHaarStatement : Prop :=
  GLTemperedFixedHaarStatement.{uF, uV} ∧
    GLLeviTemperedHaarExtensionStatement.{uF, uV}

end Langlands
