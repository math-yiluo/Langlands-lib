import Langlands.Representation.Classification.LpModCenter

/-!
# Temperedness and its separate fixed-exponent conditions

The character witness may be chosen independently at each exponent without
changing the analytic condition. The statement includes the canonical GL wrapper.
-/

namespace Langlands

universe uG uF uV

/-- Temperedness is equivalent to the separate fixed-exponent conditions at
every `2 + ε`, both at a supplied quotient Haar measure and for canonical GL
all-Haar predicates. -/
def TemperedLpStatement : Prop :=
  (∀ (G : Type uG) [Group G] [TopologicalSpace G]
      (V : Type uV) [AddCommGroup V] [Module ℂ V]
      [MeasurableSpace (G ⧸ Subgroup.center G)]
      (ρ : Representation ℂ G V)
      (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
      [MeasureTheory.Measure.IsHaarMeasure μ],
      IsTemperedModCenter ρ μ ↔
        ∀ (ε : ℝ), 0 < ε → IsLpModCenter ρ μ (2 + ε)) ∧
  (∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
      (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (ρ : Representation ℂ (GeneralLinear n F.Carrier) V),
      T.IsTempered ρ ↔ ∀ (ε : ℝ), 0 < ε → T.IsLp ρ (2 + ε))

end Langlands
