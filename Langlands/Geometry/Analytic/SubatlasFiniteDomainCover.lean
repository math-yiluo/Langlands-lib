import Langlands.Geometry.Analytic.AtlasSubatlas
import Langlands.Geometry.Analytic.OriginalDomainCompactCover
import Langlands.Geometry.Analytic.AtlasDomainCategory
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainBoundedMapGluing

/-! # Actual finite full-domain refinements through a locally refining subatlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- A finite family of selected original charts covering exactly the given
original parent. It contains no supplied algebra comparisons or output atlas. -/
structure SelectedChartCover (P : a.Index → Prop) (parent : a.Index) where
  size : ℕ
  index : Fin size → {i : a.Index // P i}
  covers : (⋃ i, Set.range (a.chart (index i).val)) = Set.range (a.chart parent)

/-- Compactness of the original parent collects the actual finite relative
neighborhood witnesses of any locally refining chart selection. -/
def selectedChartCover (P : a.Index → Prop) (hP : a.IsLocallyRefiningSelection P)
    (parent : a.Index) : a.SelectedChartCover P parent := by
  classical
  have h : AtlasTopology.LocallyRefines (a.selectedChartFamily P)
      {Set.range (a.chart parent)} := by
    intro S hS x hx
    rcases Set.mem_singleton_iff.mp hS with rfl
    exact hP _ ⟨parent, rfl⟩ x hx
  let q := h.exists_finset_cover
    (isCompact_range (a.isEmbedding_chart parent).continuous)
  let I := Classical.choose q
  have hI := Classical.choose_spec q
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  refine ⟨Fintype.card I, fun i => (e i).val, ?_⟩
  apply Eq.trans _ hI
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion₂.mpr ⟨(e i).val, (e i).property, hi⟩
  · intro hx
    obtain ⟨i, hi, hx⟩ := Set.mem_iUnion₂.mp hx
    refine Set.mem_iUnion.mpr ⟨e.symm ⟨i, hi⟩, ?_⟩
    rw [e.apply_symm_apply]
    exact hx

namespace SelectedChartCover

variable {a} {P : a.Index → Prop} {parent : a.Index}
  (c : a.SelectedChartCover P parent)

theorem subset_parent (i : Fin c.size) :
    Set.range (a.chart (c.index i).val) ⊆ Set.range (a.chart parent) := by
  rw [← c.covers]
  exact Set.subset_iUnion (fun j => Set.range (a.chart (c.index j).val)) i

/-- The actual original bounded restriction, with its full domain universal
property, represents each selected member in the unchanged parent algebra. -/
def component (i : Fin c.size) : Domain K (a.algebra parent) :=
  a.restrictionDomain (c.index i).val parent (c.subset_parent i)

@[simp]
theorem component_algebra (i : Fin c.size) :
    (c.component i).algebra = a.algebra (c.index i).val := rfl

theorem component_over_ambient (i : Fin c.size)
    (x : BanachSpectrum (a.algebra (c.index i).val)) :
    a.chart parent ((c.component i).spectrumMap x) = a.chart (c.index i).val x :=
  a.restriction_chart _ _ _ x

/-- A finite full-domain cover of the entire original parent, constructed
from its selected original chart restrictions. -/
def domainCover : Domain.FiniteCover (Domain.whole K (a.algebra parent)) where
  size := c.size
  obj := c.component
  map i := ⟨a.restriction (c.index i).val parent (c.subset_parent i),
    BoundedAlgHom.comp_id _⟩
  covers x _ := by
    have hx : a.chart parent x ∈ ⋃ i, Set.range (a.chart (c.index i).val) :=
      c.covers.symm ▸ Set.mem_range_self x
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact ⟨i, hi⟩

@[simp]
theorem domainCover_map_restriction (i : Fin c.size) :
    (c.domainCover.map i).restriction =
      a.restriction (c.index i).val parent (c.subset_parent i) := rfl

/-- Intersect the actual selected full domains with an arbitrary full
domain, then express the resulting quotient pieces over that domain algebra. -/
def algebraCover (U : Domain K (a.algebra parent)) :
    Domain.FiniteCover (Domain.whole K U.algebra) where
  size := c.size
  obj i := U.relative (U.inter (c.component i)) (U.interLeft (c.component i))
  map i := ⟨(U.interLeft (c.component i)).restriction, BoundedAlgHom.comp_id _⟩
  covers x _ := by
    obtain ⟨i, hi⟩ := c.domainCover.covers (U.spectrumMap x) (Set.mem_univ _)
    refine ⟨i, ?_⟩
    rw [U.relative_locus_eq_preimage]
    exact ⟨U.represents.hasImageIn x, hi⟩

/-- The same intersection quotient is an actual local domain of the selected
atlas, by localization through its selected original component. -/
def selectedLocalPiece (hP : a.IsLocallyRefiningSelection P)
    (U : Domain K (a.algebra parent)) (i : Fin c.size) :
    LocalDomain (a.subatlas P hP) :=
  ⟨c.index i, (c.component i).relative
    (U.inter (c.component i)) (U.interRight (c.component i))⟩

@[simp]
theorem selectedLocalPiece_algebra (hP : a.IsLocallyRefiningSelection P)
    (U : Domain K (a.algebra parent)) (i : Fin c.size) :
    (c.selectedLocalPiece hP U i).algebra = ((c.algebraCover U).obj i).algebra := rfl

/-- Both local presentations retain the identical quotient algebra and give
the same actual ambient map through their two full-domain structural maps. -/
theorem selectedLocalPiece_over_ambient (hP : a.IsLocallyRefiningSelection P)
    (U : Domain K (a.algebra parent)) (i : Fin c.size)
    (x : BanachSpectrum ((c.algebraCover U).obj i).algebra) :
    (c.selectedLocalPiece hP U i).ambientMap x =
      a.chart parent (U.spectrumMap (((c.algebraCover U).obj i).spectrumMap x)) := by
  change a.chart (c.index i).val
      ((U.interRight (c.component i)).spectrumMap x) =
    a.chart parent (U.spectrumMap ((U.interLeft (c.component i)).spectrumMap x))
  exact (c.component_over_ambient i
    ((U.interRight (c.component i)).spectrumMap x)).symm.trans
      ((congrArg (a.chart parent)
        ((U.interRight (c.component i)).spectrumMap_over_base x)).trans
          (congrArg (a.chart parent)
            ((U.interLeft (c.component i)).spectrumMap_over_base x)).symm)

/-- Every selected piece has exactly the intersection of the original
full-domain image and its selected chart range as its ambient locus. -/
theorem selectedLocalPiece_locus (hP : a.IsLocallyRefiningSelection P)
    (U : Domain K (a.algebra parent)) (i : Fin c.size) :
    (c.selectedLocalPiece hP U i).locus =
      (a.chart parent '' U.locus) ∩ Set.range (a.chart (c.index i).val) := by
  let E := c.component i
  have hmap : (a.subatlas P hP).chart (c.index i) =
      (a.chart parent).comp E.spectrumMap :=
    funext fun x => (c.component_over_ambient i x).symm
  have hL : (c.selectedLocalPiece hP U i).locus =
      a.chart parent '' (U.inter E).locus := by
    change (a.subatlas P hP).chart (c.index i) ''
      (E.relative (U.inter E) (U.interRight E)).locus = _
    rw [hmap]
    change (a.chart parent ∘ E.spectrumMap) '' _ = _
    exact (Set.image_comp _ _ _).trans
      (congrArg (Set.image (a.chart parent))
        (E.image_relative_locus (U.inter E) (U.interRight E)))
  apply hL.trans
  change a.chart parent '' (U.locus ∩
    (a.chart parent ⁻¹' Set.range (a.chart (c.index i).val))) = _
  ext x
  constructor
  · rintro ⟨y, ⟨hyU, hyE⟩, rfl⟩
    exact ⟨⟨y, hyU, rfl⟩, hyE⟩
  · rintro ⟨⟨y, hyU, rfl⟩, hyE⟩
    exact ⟨y, ⟨hyU, hyE⟩, rfl⟩

/-- Every actual local full domain is covered by the constructed selected
local-domain pieces, with no separation assumption on the ambient space. -/
theorem selectedLocalPiece_covers (hP : a.IsLocallyRefiningSelection P)
    (U : Domain K (a.algebra parent)) :
    (⋃ i, (c.selectedLocalPiece hP U i).locus) = a.chart parent '' U.locus := by
  ext x
  simp_rw [Set.mem_iUnion, c.selectedLocalPiece_locus]
  constructor
  · rintro ⟨i, hi, _⟩
    exact hi
  · intro hx
    have hxP : x ∈ Set.range (a.chart parent) := Set.image_subset_range _ _ hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (c.covers.symm ▸ hxP)
    exact ⟨i, hx, hi⟩

end SelectedChartCover

end Langlands.Analytic.IndexedAffinoidAtlas
