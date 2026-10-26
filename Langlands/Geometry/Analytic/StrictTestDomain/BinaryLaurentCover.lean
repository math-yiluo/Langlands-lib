import Langlands.Geometry.Analytic.StrictTestDomain.RationalLimits
import Langlands.Geometry.Analytic.StrictTestDomain.RationalPullbackDefinitions

/-! # Binary unit-radius Laurent rational inputs -/

noncomputable section

universe u

namespace Langlands.Analytic.StrictTestDomain.RationalData

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {P Q : PresentedStrictAffinoidAlgebra K}

/-- The rational input for the Laurent domain `x f ≤ 1`. -/
def laurentUpper (f : P) : RationalData K P where
  arity := 1
  denominator := 1
  numerator _ := f
  no_common_zero x := Or.inl (by
    rw [map_one]
    exact one_ne_zero)

/-- The rational input for the Laurent domain `1 ≤ x f`. -/
def laurentLower (f : P) : RationalData K P where
  arity := 1
  denominator := f
  numerator _ := 1
  no_common_zero x := Or.inr ⟨0, by
    rw [map_one]
    exact one_ne_zero⟩

@[simp]
theorem laurentUpper_arity (f : P) : (laurentUpper f).arity = 1 := rfl

@[simp]
theorem laurentUpper_denominator (f : P) : (laurentUpper f).denominator = 1 := rfl

@[simp]
theorem laurentUpper_numerator (f : P) (j : Fin 1) :
    (laurentUpper f).numerator j = f := rfl

@[simp]
theorem laurentLower_arity (f : P) : (laurentLower f).arity = 1 := rfl

@[simp]
theorem laurentLower_denominator (f : P) : (laurentLower f).denominator = f := rfl

@[simp]
theorem laurentLower_numerator (f : P) (j : Fin 1) :
    (laurentLower f).numerator j = 1 := rfl

@[simp]
theorem mem_locus_laurentUpper (f : P) (x : BanachSpectrum P) :
    x ∈ (laurentUpper f).locus ↔ x f ≤ 1 := by
  simp [locus, RationalLocalization.locus, laurentUpper]

@[simp]
theorem mem_locus_laurentLower (f : P) (x : BanachSpectrum P) :
    x ∈ (laurentLower f).locus ↔ 1 ≤ x f := by
  simp [locus, RationalLocalization.locus, laurentLower]

/-- Each actual spectrum point belongs to at least one binary Laurent locus. -/
theorem mem_laurentUpper_or_mem_laurentLower (f : P) (x : BanachSpectrum P) :
    x ∈ (laurentUpper f).locus ∨ x ∈ (laurentLower f).locus := by
  simpa only [mem_locus_laurentUpper, mem_locus_laurentLower] using le_total (x f) 1

@[simp]
theorem locus_laurentUpper_union_laurentLower (f : P) :
    (laurentUpper f).locus ∪ (laurentLower f).locus = Set.univ := by
  ext x
  simp only [Set.mem_union, Set.mem_univ, iff_true]
  exact mem_laurentUpper_or_mem_laurentLower f x

/-- Mapping the upper inputs gives exactly the upper inputs of the image. -/
@[simp]
theorem pullback_laurentUpper (f : P) (φ : BoundedAlgHom K P Q) :
    (laurentUpper f).pullback φ = laurentUpper (φ f) := by
  simp only [pullback, laurentUpper, map_one]

/-- Mapping the lower inputs gives exactly the lower inputs of the image. -/
@[simp]
theorem pullback_laurentLower (f : P) (φ : BoundedAlgHom K P Q) :
    (laurentLower f).pullback φ = laurentLower (φ f) := by
  simp only [pullback, laurentLower, map_one]

variable [CompleteSpace K]

/-- The overlap uses the existing rational intersection presentation. -/
@[simp]
theorem mem_locus_inter_laurentUpper_laurentLower (f : P) (x : BanachSpectrum P) :
    x ∈ ((laurentUpper f).inter (laurentLower f)).locus ↔ x f = 1 := by
  rw [locus_inter]
  simp only [Set.mem_inter_iff, mem_locus_laurentUpper, mem_locus_laurentLower]
  exact le_antisymm_iff.symm

end Langlands.Analytic.StrictTestDomain.RationalData
