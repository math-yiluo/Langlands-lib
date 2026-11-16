import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalFixedCoefficientFiniteness

/-! # The actual discrete-series coefficient sum with fixed central character

This is the algebraic sum `A₂(G)_χ` in Waldspurger VIII.4. Its summands are the
published canonical coefficient spaces. No assertion about cuspidal Schwartz
functions or their central projections is assumed.
-/

noncomputable section

open CategoryTheory MeasureTheory
open Langlands.Plancherel

namespace Langlands.HarishChandraSchwartz

universe uG uV uW

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Actual coefficient tensor transport identifies the spaces of equivalent smooth
representations, including representations in different carrier universes. -/
theorem coefficientFunctionSpace_eq_of_equiv
    {π : SmoothRep.{0, uG, uV} ℂ G} {τ : SmoothRep.{0, uG, uW} ℂ G}
    (e : π.representation.Equiv τ.representation) :
    coefficientFunctionSpace π = coefficientFunctionSpace τ := by
  rw [coefficientFunctionSpace_eq_map, coefficientFunctionSpace_eq_map]
  congr 1
  apply le_antisymm
  · rintro f ⟨t, rfl⟩
    exact ⟨coefficientTensorCongr e t, coefficientTensorMap_congr e t⟩
  · rintro f ⟨t, rfl⟩
    exact ⟨coefficientTensorCongr e.symm t, coefficientTensorMap_congr e.symm t⟩

/-- The coefficient space of any representative of a smooth-dual class equals
the coefficient space of its canonical `Quotient.out` representative. -/
theorem coefficientFunctionSpace_eq_out_of_class_eq
    (π : IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G))
    (ω : SmoothDualClass.{0, uG, uV} (k := ℂ) (G := G))
    (hπ : Quotient.mk _ π = ω) :
    coefficientFunctionSpace π.obj = coefficientFunctionSpace ω.out.obj := by
  obtain ⟨e⟩ := Quotient.exact (hπ.trans (Quotient.out_eq ω).symm)
  exact coefficientFunctionSpace_eq_of_equiv
    (SmoothRep.equivOfIso ((irreducibleAdmissibleProperty (k := ℂ) (G := G)).ι.mapIso e))

variable (A : Subgroup G) [A.Normal] (hA : A ≤ Subgroup.center G)
  [MeasurableSpace (G ⧸ A)] (mu : Measure (G ⧸ A)) [mu.IsHaarMeasure]
  (χ : A →* ℂˣ)

/-- Waldspurger's `A₂(G)_χ`: the algebraic sum of all discrete-series coefficient
spaces whose central character on the prescribed quotient subgroup is `χ`. -/
def discreteSeriesCentralCoefficientSpace : Submodule ℂ (G → ℂ) :=
  ⨆ ω : {ω : DiscreteSeriesClass.{uG, uV} A hA mu | classActsByCharacter A χ ω.val},
    coefficientFunctionSpace ω.val.val.out.obj

theorem coefficientFunctionSpace_le_discreteSeriesCentralCoefficientSpace
    (ω : DiscreteSeriesClass.{uG, uV} A hA mu)
    (hω : classActsByCharacter A χ ω.val) :
    coefficientFunctionSpace ω.val.out.obj ≤
      discreteSeriesCentralCoefficientSpace.{uG, uV} A hA mu χ :=
  le_iSup (fun ω :
    {ω : DiscreteSeriesClass.{uG, uV} A hA mu | classActsByCharacter A χ ω.val} =>
      coefficientFunctionSpace ω.val.val.out.obj) ⟨ω, hω⟩

theorem matrixCoefficient_mem_discreteSeriesCentralCoefficientSpace
    (ω : DiscreteSeriesClass.{uG, uV} A hA mu)
    (hω : classActsByCharacter A χ ω.val)
    (ℓ : SmoothDual ω.val.out.obj.representation) (v : ω.val.out.obj) :
    matrixCoefficient ω.val.out.obj.representation ℓ.val v ∈
      discreteSeriesCentralCoefficientSpace.{uG, uV} A hA mu χ :=
  coefficientFunctionSpace_le_discreteSeriesCentralCoefficientSpace A hA mu χ ω hω
    (matrixCoefficient_mem_coefficientFunctionSpace _ ℓ v)

theorem discreteSeriesCentralCoefficientSpace_le_iff (E : Submodule ℂ (G → ℂ)) :
    discreteSeriesCentralCoefficientSpace.{uG, uV} A hA mu χ ≤ E ↔
      ∀ ω : DiscreteSeriesClass.{uG, uV} A hA mu,
        classActsByCharacter A χ ω.val → coefficientFunctionSpace ω.val.out.obj ≤ E := by
  constructor
  · intro h ω hω
    exact (coefficientFunctionSpace_le_discreteSeriesCentralCoefficientSpace
      A hA mu χ ω hω).trans h
  · intro h
    exact iSup_le fun ω => h ω.val ω.property

/-- Changing every irreducible admissible representative leaves the actual
algebraic coefficient sum unchanged. -/
theorem discreteSeriesCentralCoefficientSpace_eq_iSup_representatives
    (π : DiscreteSeriesClass.{uG, uV} A hA mu →
      IrreducibleAdmissibleRep.{0, uG, uV} (k := ℂ) (G := G))
    (hπ : ∀ ω, Quotient.mk _ (π ω) = ω.val) :
    discreteSeriesCentralCoefficientSpace.{uG, uV} A hA mu χ =
      ⨆ ω : {ω : DiscreteSeriesClass.{uG, uV} A hA mu | classActsByCharacter A χ ω.val},
        coefficientFunctionSpace (π ω.val).obj := by
  apply iSup_congr
  intro ω
  exact (coefficientFunctionSpace_eq_out_of_class_eq (π ω.val) ω.val.val (hπ ω.val)).symm

/-- The coefficient sum is direct, by the existing independence theorem for
pairwise inequivalent irreducible smooth representations. -/
theorem iSupIndep_discreteSeriesCentralCoefficientSpace :
    iSupIndep fun ω :
      {ω : DiscreteSeriesClass.{uG, uV} A hA mu | classActsByCharacter A χ ω.val} =>
        coefficientFunctionSpace ω.val.val.out.obj := by
  refine iSupIndep_coefficientFunctionSpace (fun ω :
    {ω : DiscreteSeriesClass.{uG, uV} A hA mu | classActsByCharacter A χ ω.val} =>
      ω.val.val.out.obj)
    (fun ω => ω.val.val.out.property.1) ?_
  rintro ω η ⟨e⟩
  have h : ω.val.val = η.val.val := by
    rw [← Quotient.out_eq ω.val.val, ← Quotient.out_eq η.val.val]
    exact Quotient.sound ⟨IrreducibleAdmissibleRep.isoMk (SmoothRep.mkIso e)⟩
  exact Subtype.ext (Subtype.ext h)

/-- The existing least fixed coefficient span lies in this full coefficient sum. -/
theorem discreteSeriesCentralFixedCoefficientSpace_le (H : Subgroup G) :
    discreteSeriesCentralFixedCoefficientSpace.{uG, uV} A hA mu χ H ≤
      discreteSeriesCentralCoefficientSpace.{uG, uV} A hA mu χ := by
  apply (discreteSeriesCentralFixedCoefficientSpace_le_iff A hA mu χ H _).mpr
  intro ω hω f hf _
  exact coefficientFunctionSpace_le_discreteSeriesCentralCoefficientSpace A hA mu χ ω hω.1 hf

end Langlands.HarishChandraSchwartz
