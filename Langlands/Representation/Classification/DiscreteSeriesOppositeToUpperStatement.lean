import Langlands.Representation.Classification.Tempered
import Langlands.Representation.Induction.OppositeParabolic
import Mathlib.RepresentationTheory.Semisimple

/-!
# Same-sigma opposite-to-upper discrete-series induction comparison

This proposition retains the actual product-Levi representation in both
normalized function inductions. It isolates opposite semisimplicity and
transport of a given tempered embedding from the larger summand statement.
-/

namespace Langlands

universe uF uV uW

/-- For the same discrete-series representation of the actual product Levi,
an opposite-induction embedding of an irreducible tempered representation
implies opposite semisimplicity and an upper-induction embedding. -/
def GLTemperedDiscreteSeriesOppositeToUpperStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData),
    letI := T.topology
    ∀ (n : ℕ), 0 < n → ∀ B : GeneralLinear.BlockShape n,
      letI := T.leviTopologicalGroup B
      let M := B.Levi F.Carrier
      let Q := M ⧸ Subgroup.center M
      ∀ [MeasurableSpace Q] [BorelSpace Q]
        (μ : MeasureTheory.Measure Q) [MeasureTheory.Measure.IsHaarMeasure μ]
        (V : Type uV) [AddCommGroup V] [Module ℂ V]
        (W : Type uW) [AddCommGroup W] [Module ℂ W]
        (π : Representation ℂ (GeneralLinear n F.Carrier) V)
        (σ : Representation ℂ M W),
        Representation.IsIrreducible π → T.IsTempered π →
        Representation.IsIrreducible σ → IsSquareIntegrableModCenter σ μ →
          (∃ j : π.IntertwiningMap (T.normalizedOppositeParabolicInduced B σ),
            Function.Injective j) →
          (Representation.IsSemisimpleRepresentation
              (T.normalizedOppositeParabolicInduced B σ) ∧
            ∃ j : π.IntertwiningMap (T.normalizedParabolicInduced B σ),
              Function.Injective j)

end Langlands
