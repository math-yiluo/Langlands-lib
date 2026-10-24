import Langlands.Representation.MatrixCoefficient.NormRegularityStatement
import Langlands.Representation.MatrixCoefficient.LawsProof

/-! # Continuity and measurability of descended coefficient norms -/

namespace Langlands

namespace UnitaryCentralCharacter

variable {G V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  (c : UnitaryCentralCharacter ρ) (ℓ : Module.Dual ℂ V) (v : V)

theorem continuous_coefficientNorm (hv : IsSmoothVector ρ v) :
    Continuous (c.coefficientNorm ℓ v) := by
  apply (QuotientGroup.isQuotientMap_mk (Subgroup.center G)).continuous_iff.mpr
  exact (matrixCoefficient_isLocallyConstant ρ ℓ v hv).continuous.norm

theorem aestronglyMeasurable_coefficientNorm
    [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
    (hv : IsSmoothVector ρ v) (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G)) :
    MeasureTheory.AEStronglyMeasurable (c.coefficientNorm ℓ v) μ :=
  (c.continuous_coefficientNorm ℓ v hv).aestronglyMeasurable

end UnitaryCentralCharacter

theorem coefficientNormRegularity.{uG, uV} : CoefficientNormRegularityStatement.{uG, uV} := by
  intro G V _ _ _ _ _ ρ c ℓ v hv
  refine ⟨c.continuous_coefficientNorm ℓ v hv, ?_⟩
  intro _ _ μ
  exact c.aestronglyMeasurable_coefficientNorm ℓ v hv μ

end Langlands
