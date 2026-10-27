import Langlands.Representation.Classification.TemperedModCenterHaarStatement
import Langlands.Analysis.HaarLpProof

/-! # Haar normalization invariance of temperedness modulo the center -/

namespace Langlands

universe uG uV

section Generic

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [LocallyCompactSpace (G ⧸ Subgroup.center G)]
variable [SecondCountableTopology (G ⧸ Subgroup.center G)]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable [MeasurableSpace (G ⧸ Subgroup.center G)]
variable [BorelSpace (G ⧸ Subgroup.center G)]

/-- On one Borel central quotient, changing the Haar normalization preserves
analytic temperedness with the same unitary central-character witness. -/
theorem isTemperedModCenter_iff_haar (ρ : Representation ℂ G V)
    (μ ν : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] [MeasureTheory.Measure.IsHaarMeasure ν] :
    IsTemperedModCenter ρ μ ↔ IsTemperedModCenter ρ ν := by
  constructor
  · rintro ⟨hρ, c, hc⟩
    refine ⟨hρ, c, ?_⟩
    intro ℓ v ε hε
    exact (haarMemLpInvariant _ μ ν (c.coefficientNorm ℓ v)
      (ENNReal.ofReal (2 + ε))).mp (hc ℓ v ε hε)
  · rintro ⟨hρ, c, hc⟩
    refine ⟨hρ, c, ?_⟩
    intro ℓ v ε hε
    exact (haarMemLpInvariant _ μ ν (c.coefficientNorm ℓ v)
      (ENNReal.ofReal (2 + ε))).mpr (hc ℓ v ε hε)

end Generic

/-- The closed generic Haar-normalization invariance statement. -/
theorem temperedModCenterHaarInvariant :
    TemperedModCenterHaarInvariantStatement.{uG, uV} := by
  intro G _ _ _ _ _ V _ _ _ _ ρ μ ν _ _
  exact isTemperedModCenter_iff_haar ρ μ ν

end Langlands
