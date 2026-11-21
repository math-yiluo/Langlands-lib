import Langlands.HarmonicAnalysis.HarishChandraSchwartz.DiscreteSeriesCentralCoefficientSpace
import Langlands.Representation.Smooth.SmallRealizationProof

/-! # Discrete series in independent carrier universes -/

noncomputable section

universe uG uV uW

open MeasureTheory TopologicalSpace
open Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] (mu : Measure (G ⧸ A)) [mu.IsHaarMeasure]

/-- Every actual discrete-series class has a realization with carrier in the
independently prescribed universe `uV` and the same central quotient measure. -/
def DiscreteSeriesSmallRealizationStatement : Prop :=
  ∀ [SeparableSpace G] (ω : DiscreteSeriesClass.{uG, uW} A hA mu),
    ∃ π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G),
      IsSquareIntegrableModCentralSubgroup A hA π.obj.representation mu ∧
        Nonempty (ω.val.out.obj.representation.Equiv π.obj.representation)

/-- Small realization preserves square integrability on the given quotient. -/
theorem discreteSeriesSmallRealization :
    DiscreteSeriesSmallRealizationStatement.{uG, uV, uW} A hA mu := by
  intro _ ω
  have hsq : IsSquareIntegrableModCentralSubgroup A hA ω.val.out.obj.representation mu := by
    change IsDiscreteSeriesClass A hA mu (Quotient.mk _ ω.val.out)
    rw [Quotient.out_eq ω.val]
    exact ω.property
  obtain ⟨π, hirr, ⟨e⟩⟩ :
      ∃ π : SmoothRep.{0, uG, uV} ℂ G,
        π.IsIrreducible ∧ Nonempty (ω.val.out.obj.representation.Equiv π.representation) :=
    exists_irreducible_smoothRep_equiv_of_separable ω.val.out.obj ω.val.out.property.1
  have hsq' := (isSquareIntegrableModCentralSubgroup_iff_of_equiv A hA e mu).mp hsq
  exact ⟨⟨π, hirr, hsq'.1⟩, hsq', ⟨e⟩⟩

variable [SeparableSpace G]

private theorem discreteSeriesCentralCoefficientSpace_le_of_separable (χ : A →* ℂˣ) :
    discreteSeriesCentralCoefficientSpace.{uG, uW} A hA mu χ ≤
      discreteSeriesCentralCoefficientSpace.{uG, uV} A hA mu χ := by
  apply (discreteSeriesCentralCoefficientSpace_le_iff A hA mu χ _).mpr
  intro ω hω
  obtain ⟨π, hsq, ⟨e⟩⟩ := discreteSeriesSmallRealization.{uG, uV, uW} A hA mu ω
  let ω' := discreteSeriesClass A hA mu π hsq
  have hχ : ∀ (a : A) (v : ω.val.out.obj),
      ω.val.out.obj.representation a v = (χ a : ℂ) • v := by
    apply (classActsByCharacter_mk A χ ω.val.out).mp
    rw [Quotient.out_eq ω.val]
    exact hω
  have hχ' : classActsByCharacter A χ ω'.val :=
    (classActsByCharacter_mk A χ π).mpr (actsByCharacter_of_equiv e A χ hχ)
  rw [coefficientFunctionSpace_eq_of_equiv e,
    coefficientFunctionSpace_eq_out_of_class_eq π ω'.val rfl]
  exact coefficientFunctionSpace_le_discreteSeriesCentralCoefficientSpace A hA mu χ ω' hχ'

/-- The actual coefficient sum of VIII.4 is independent of the carrier
universe on a separable group, with the same subgroup, measure and character. -/
theorem discreteSeriesCentralCoefficientSpace_eq_of_separable (χ : A →* ℂˣ) :
    discreteSeriesCentralCoefficientSpace.{uG, uV} A hA mu χ =
      discreteSeriesCentralCoefficientSpace.{uG, uW} A hA mu χ :=
  le_antisymm
    (discreteSeriesCentralCoefficientSpace_le_of_separable A hA mu χ)
    (discreteSeriesCentralCoefficientSpace_le_of_separable A hA mu χ)

end Langlands.HarishChandraSchwartz
