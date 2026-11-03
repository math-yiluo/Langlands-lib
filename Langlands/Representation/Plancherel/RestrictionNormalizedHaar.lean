import Langlands.Representation.Plancherel.FiniteCharacterQuotientMeasure
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.Spherical

/-! # Haar measure normalized by a finite-kernel restriction -/

noncomputable section

open Function Set Topology MeasureTheory MeasureTheory.Measure
open Langlands.HarishChandraSchwartz
open scoped ENNReal

namespace Langlands.Plancherel

variable {C D : Type*} [CommGroup C] [CommGroup D]
  [TopologicalSpace C] [IsTopologicalGroup C] [CompactSpace C] [T2Space C]
  [TopologicalSpace D] [IsTopologicalGroup D] [CompactSpace D] [T2Space D]
  [MeasurableSpace C] [BorelSpace C] [MeasurableSpace D] [BorelSpace D]

/-- The character Haar measure whose mass counts the finite restriction kernel. -/
def restrictionNormalizedHaar (f : C →ₜ* D) [Finite f.toMonoidHom.ker] : Measure C :=
  (Nat.card f.toMonoidHom.ker : ℝ≥0∞) • normalizedHaar C

instance instRestrictionNormalizedHaar1 (f : C →ₜ* D) [Finite f.toMonoidHom.ker] :
    IsHaarMeasure (restrictionNormalizedHaar f) := by
  apply IsHaarMeasure.smul (normalizedHaar C)
  · exact_mod_cast (Nat.card_pos (α := f.toMonoidHom.ker)).ne'
  · simp

omit [T2Space C] [IsTopologicalGroup D] [CompactSpace D] [T2Space D]
    [MeasurableSpace D] [BorelSpace D] in
theorem restrictionNormalizedHaar_apply (f : C →ₜ* D) [Finite f.toMonoidHom.ker]
    (E : Set C) :
    restrictionNormalizedHaar f E =
      (Nat.card f.toMonoidHom.ker : ℝ≥0∞) * normalizedHaar C E := rfl

omit [T2Space C] [IsTopologicalGroup D] [CompactSpace D] [T2Space D]
    [MeasurableSpace D] [BorelSpace D] in
@[simp]
theorem restrictionNormalizedHaar_univ (f : C →ₜ* D) [Finite f.toMonoidHom.ker] :
    restrictionNormalizedHaar f univ = (Nat.card f.toMonoidHom.ker : ℝ≥0∞) := by
  simp [restrictionNormalizedHaar]

omit [T2Space C] [T2Space D] in
/-- Globally, pushforward counts the kernel; local preservation has no such factor. -/
theorem map_restrictionNormalizedHaar (f : C →ₜ* D) [Finite f.toMonoidHom.ker]
    (hf : Surjective f) :
    Measure.map f (restrictionNormalizedHaar f) =
      (Nat.card f.toMonoidHom.ker : ℝ≥0∞) • normalizedHaar D := by
  rw [restrictionNormalizedHaar,
    Measure.map_smul (f := (f : C → D)) _ f.continuous.measurable.aemeasurable]
  congr 1
  exact (f.toMonoidHom.measurePreserving f.continuous hf (by simp)).map_eq

private def compactQuotientKerHomeomorph (f : C →ₜ* D) (hf : Surjective f) :
    (C ⧸ f.toMonoidHom.ker) ≃ₜ D := by
  let e := QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom hf
  have he : Continuous e := by
    apply (QuotientGroup.isQuotientMap_mk f.toMonoidHom.ker).continuous_iff.mpr
    exact f.continuous
  exact e.toEquiv.toHomeomorphOfContinuousClosed he he.isClosedMap

/-- A finite-kernel surjection locally preserves the restriction-normalized
Haar measure and the target's probability Haar measure. -/
theorem isLocallyMeasurePreserving_restrictionNormalizedHaar
    (f : C →ₜ* D) [Finite f.toMonoidHom.ker] (hf : Surjective f) :
    IsLocallyMeasurePreserving f (restrictionNormalizedHaar f) (normalizedHaar D) := by
  let S := f.toMonoidHom.ker
  let q : C → C ⧸ S := QuotientGroup.mk
  let e := compactQuotientKerHomeomorph f hf
  let : MeasurableSpace (C ⧸ S) := borel _
  let : BorelSpace (C ⧸ S) := ⟨rfl⟩
  have heq : e ∘ q = f := rfl
  have hcard : (Nat.card S : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (Nat.card_pos (α := S)).ne'
  have hmap : Measure.map e (finiteCharacterQuotientMeasure S
      (restrictionNormalizedHaar f)) = normalizedHaar D := by
    rw [finiteCharacterQuotientMeasure,
      Measure.map_smul _ e.continuous.measurable.aemeasurable,
      Measure.map_map e.continuous.measurable QuotientGroup.continuous_mk.measurable,
      heq, map_restrictionNormalizedHaar f hf, smul_smul]
    rw [ENNReal.inv_mul_cancel hcard (by simp), one_smul]
  intro x
  obtain ⟨U, hU, hx, hinj, hmeasure⟩ :=
    isLocallyMeasurePreserving_finiteCharacterQuotient S (restrictionNormalizedHaar f) x
  refine ⟨U, hU, hx, ?_, ?_⟩
  · rw [← heq]
    exact e.injective.injOn.comp hinj (mapsTo_univ _ _)
  · intro E hE hsub
    obtain ⟨himage, hvalue⟩ := hmeasure E hE hsub
    have hm : MeasurableSet (e '' (q '' E)) :=
      e.measurableEmbedding.measurableSet_image' himage
    rw [← heq, image_comp]
    refine ⟨hm, ?_⟩
    rw [← hmap, Measure.map_apply e.continuous.measurable hm,
      e.injective.preimage_image]
    exact hvalue

end Langlands.Plancherel
