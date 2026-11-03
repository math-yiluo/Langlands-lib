import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainContainedOpenRestriction

/-! # Original stalk maps over the interior of a full domain -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain

open CategoryTheory RationalChart TopologicalSpace Topology
open AlgebraicGeometry

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K} (d : Domain K A)

set_option backward.isDefEq.respectTransparency false in
/-- The original algebra-stalk map is invertible at every point over an
ordinary open contained in the represented locus. -/
theorem openStalkMap_isIso_of_mem_open (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus)
    (y : BanachSpectrum d.algebra) (hy : d.spectrumMap y ∈ U) :
    IsIso (openStalkMap d.baseMap y) := by
  let x : d.preimageOpen U := ⟨y, hy⟩
  let := d.algebraSheafedSpaceMapOnOpen_isOpenImmersion U hU
  have hcomp := SheafedSpace.IsOpenImmersion.stalk_iso
    (d.algebraSheafedSpaceMapOnOpen U) x
  change IsIso ((((algebraSheafedSpace K d.algebra).ofRestrict
    (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum d.algebra))
      (d.preimageOpen U))).hom ≫
    (algebraSheafedSpaceMap d.baseMap).hom).stalkMap x) at hcomp
  rw [PresheafedSpace.stalkMap.comp] at hcomp
  exact (isIso_comp_right_iff (openStalkMap d.baseMap y)
    (((algebraSheafedSpace K d.algebra).ofRestrict
      (Opens.isOpenEmbedding (X := TopCat.of (BanachSpectrum d.algebra))
        (d.preimageOpen U))).hom.stalkMap x)).mp hcomp

/-- Scalar forgetting and the genuine stalk comparisons preserve the
invertibility of the original ring-stalk map on a contained ordinary open. -/
theorem openRingStalkMap_isIso_of_mem_open (U : Opens (BanachSpectrum A))
    (hU : (U : Set (BanachSpectrum A)) ⊆ d.locus)
    (y : BanachSpectrum d.algebra) (hy : d.spectrumMap y ∈ U) :
    IsIso (openRingStalkMap d.baseMap y) := by
  let := d.openStalkMap_isIso_of_mem_open U hU y hy
  rw [openRingStalkMap_eq]
  infer_instance

/-- Whole-locus openness is unnecessary for the original algebra-stalk map
at a point whose image belongs to the interior. -/
theorem openStalkMap_isIso_of_mem_interior (y : BanachSpectrum d.algebra)
    (hy : d.spectrumMap y ∈ interior d.locus) :
    IsIso (openStalkMap d.baseMap y) :=
  d.openStalkMap_isIso_of_mem_open ⟨interior d.locus, isOpen_interior⟩
    interior_subset y hy

/-- The original ring-stalk map is likewise invertible over the interior. -/
theorem openRingStalkMap_isIso_of_mem_interior (y : BanachSpectrum d.algebra)
    (hy : d.spectrumMap y ∈ interior d.locus) :
    IsIso (openRingStalkMap d.baseMap y) :=
  d.openRingStalkMap_isIso_of_mem_open ⟨interior d.locus, isOpen_interior⟩
    interior_subset y hy

/-- Canonical comparison of the actual ordinary-open algebra stalks over the
interior, with the original stalk map as forward morphism. -/
def openInteriorStalkIso (y : BanachSpectrum d.algebra)
    (hy : d.spectrumMap y ∈ interior d.locus) :
    openStalk (d.spectrumMap y) ≅ openStalk y := by
  exact @asIso _ _ _ _ (openStalkMap d.baseMap y)
    (d.openStalkMap_isIso_of_mem_interior y hy)

@[simp]
theorem openInteriorStalkIso_hom (y : BanachSpectrum d.algebra)
    (hy : d.spectrumMap y ∈ interior d.locus) :
    (d.openInteriorStalkIso y hy).hom = openStalkMap d.baseMap y := rfl

/-- Canonical comparison of the actual ring stalks of the original locally
ringed-space morphism over the interior. -/
def openInteriorRingStalkIso (y : BanachSpectrum d.algebra)
    (hy : d.spectrumMap y ∈ interior d.locus) :
    TopCat.Presheaf.stalk (openRingPresheaf K A) (d.spectrumMap y) ≅
      TopCat.Presheaf.stalk (openRingPresheaf K d.algebra) y := by
  exact @asIso _ _ _ _ (openRingStalkMap d.baseMap y)
    (d.openRingStalkMap_isIso_of_mem_interior y hy)

@[simp]
theorem openInteriorRingStalkIso_hom (y : BanachSpectrum d.algebra)
    (hy : d.spectrumMap y ∈ interior d.locus) :
    (d.openInteriorRingStalkIso y hy).hom = openRingStalkMap d.baseMap y := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain
