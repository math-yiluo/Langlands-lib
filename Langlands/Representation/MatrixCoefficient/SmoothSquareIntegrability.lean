import Langlands.Representation.Category.Twist
import Langlands.Representation.MatrixCoefficient.ModuloCenter

/-!
# Square-integrability of smooth representations without admissibility

Renard IV.3.2 defines square-integrability before proving admissibility of the
irreducible objects. These predicates retain that distinction and allow arbitrary
smooth character twists.
-/

noncomputable section

namespace Langlands.SmoothRep

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable [MeasurableSpace (G ⧸ Subgroup.center G)]

/-- The all-coefficients condition of Renard IV.3.2 for a smooth representation.
Admissibility and irreducibility are not part of this predicate. -/
def IsSquareIntegrableModuloCenter [IsTopologicalGroup G]
    [BorelSpace (G ⧸ Subgroup.center G)] (π : SmoothRep.{0, uG, uV} ℂ G)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] : Prop :=
  ∃ c : UnitaryCentralCharacter π.representation,
    ∀ (ℓ : SmoothDual π.representation) (x : π),
      MeasureTheory.MemLp (c.coefficientNorm ℓ x) 2 μ

/-- Renard IV.3.2 essential square-integrability: some arbitrary smooth character
twist satisfies the all-coefficients condition. -/
def IsEssentiallySquareIntegrableModuloCenter [IsTopologicalGroup G]
    [BorelSpace (G ⧸ Subgroup.center G)] (π : SmoothRep.{0, uG, uV} ℂ G)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] : Prop :=
  ∃ (ω : G →* ℂˣ) (hω : IsOpen (ω.ker : Set G)),
    (π.twist ω hω).IsSquareIntegrableModuloCenter μ

variable [IsTopologicalGroup G] [BorelSpace (G ⧸ Subgroup.center G)]

/-- The existing admissibility-bearing predicate is precisely admissibility
conjoined with the source all-coefficients condition. -/
theorem isSquareIntegrableModCenter_iff (π : SmoothRep.{0, uG, uV} ℂ G)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] :
    Langlands.IsSquareIntegrableModCenter π.representation μ ↔
      π.IsAdmissible ∧ π.IsSquareIntegrableModuloCenter μ :=
  Iff.rfl

/-- The trivial character witnesses essential square-integrability. -/
theorem IsSquareIntegrableModuloCenter.isEssentiallySquareIntegrableModuloCenter
    {π : SmoothRep.{0, uG, uV} ℂ G}
    {μ : MeasureTheory.Measure (G ⧸ Subgroup.center G)}
    [MeasureTheory.Measure.IsHaarMeasure μ] (h : π.IsSquareIntegrableModuloCenter μ) :
    π.IsEssentiallySquareIntegrableModuloCenter μ := by
  have h1 : IsOpen ((1 : G →* ℂˣ).ker : Set G) := by
    simp
  refine ⟨1, h1, ?_⟩
  change ∃ c : UnitaryCentralCharacter (Langlands.twist 1 π.representation),
    ∀ (ℓ : SmoothDual (Langlands.twist 1 π.representation)) (x : π),
      MeasureTheory.MemLp (c.coefficientNorm ℓ x) 2 μ
  rw [Langlands.twist_one]
  exact h

/-- For an admissible object, arbitrary smooth twists may be tested using the
existing admissibility-bearing square-integrability predicate. -/
theorem isEssentiallySquareIntegrableModuloCenter_iff_of_isAdmissible
    (π : SmoothRep.{0, uG, uV} ℂ G)
    (μ : MeasureTheory.Measure (G ⧸ Subgroup.center G))
    [MeasureTheory.Measure.IsHaarMeasure μ] (hπ : π.IsAdmissible) :
    π.IsEssentiallySquareIntegrableModuloCenter μ ↔
      ∃ (ω : G →* ℂˣ) (hω : IsOpen (ω.ker : Set G)),
        Langlands.IsSquareIntegrableModCenter (π.twist ω hω).representation μ := by
  constructor
  · rintro ⟨ω, hω, h⟩
    exact ⟨ω, hω, (isAdmissible_twist_iff ω hω π).mpr hπ, h⟩
  · rintro ⟨ω, hω, _, h⟩
    exact ⟨ω, hω, h⟩

end Langlands.SmoothRep
