import Langlands.Representation.MatrixCoefficient.ModuloCenter

/-! # Regularity of matrix-coefficient norms on the central quotient -/

namespace Langlands

/-- A smooth vector gives a continuous descended coefficient norm. With the
Borel measurable structure, that function is almost everywhere strongly
measurable for every measure on the actual quotient by the center. -/
def CoefficientNormRegularityStatement.{uG, uV} : Prop :=
  ∀ (G : Type uG) (V : Type uV) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (c : UnitaryCentralCharacter ρ)
    (ℓ : Module.Dual ℂ V) (v : V),
    IsSmoothVector ρ v →
      Continuous (c.coefficientNorm ℓ v) ∧
        ∀ [MeasurableSpace (G ⧸ Subgroup.center G)]
          [BorelSpace (G ⧸ Subgroup.center G)]
          (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G)),
          MeasureTheory.AEStronglyMeasurable (c.coefficientNorm ℓ v) μ

end Langlands
