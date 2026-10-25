import Langlands.Representation.Classification.TemperedInductionStatement

/-!
# Preservation of analytic temperedness by normalized GL induction

This proposition isolates the final conclusion of `GLTemperedInductionStatement`
with exactly its input quantifiers and hypotheses. The induction is the actual
positive-half-modulus upper parabolic induction, acting by right translation.
-/

namespace Langlands

universe uF uV

/-- Normalized induction from an irreducible analytically tempered representation
of the actual block Levi is analytically tempered. -/
def GLTemperedInductionPreservationStatement : Prop :=
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
          T.IsTempered (T.normalizedParabolicInduced B σ)

end Langlands
