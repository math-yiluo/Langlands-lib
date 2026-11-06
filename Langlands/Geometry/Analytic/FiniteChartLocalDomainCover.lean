import Langlands.Geometry.Analytic.FiniteChartSubordinateCover
import Langlands.Geometry.Analytic.AtlasDomainCategory

/-! # Finite full-domain covers subordinate to a Hausdorff chart union -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  (d : FiniteChartGluingData a)

/-- A full local domain contained in the Hausdorff union meets each defining
chart compactly, with no separation assumption on the ambient space. -/
theorem isCompact_localDomain_inter_member [T2Space d.locus] (U : LocalDomain a)
    (hU : U.locus ⊆ d.locus) (i : Fin d.size) :
    IsCompact (U.locus ∩ Set.range (a.chart (d.index i))) := by
  have h₁ : IsCompact (Subtype.val ⁻¹' U.locus : Set d.locus) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' U.isCompact_locus
      (by simpa only [Subtype.range_coe] using hU)
  have h₂ : IsCompact
      (Subtype.val ⁻¹' Set.range (a.chart (d.index i)) : Set d.locus) :=
    Topology.IsInducing.subtypeVal.isCompact_preimage'
      (isCompact_range (a.isEmbedding_chart (d.index i)).continuous)
      (by
        simpa only [Subtype.range_coe, locus] using
          (Set.subset_iUnion (fun j => Set.range (a.chart (d.index j))) i))
  have heq : Subtype.val ''
      ((Subtype.val ⁻¹' U.locus : Set d.locus) ∩
        Subtype.val ⁻¹' Set.range (a.chart (d.index i))) =
      U.locus ∩ Set.range (a.chart (d.index i)) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hU hx.1⟩, hx, rfl⟩
  rw [← heq]
  exact (h₁.inter h₂).image continuous_subtype_val

/-- A concrete finite full-domain cover of U, together with a defining union
member containing each covering piece's literal ambient locus. -/
structure SubordinateLocalDomainCover (U : LocalDomain a) where
  cover : Domain.FiniteCover U.domain
  member : Fin cover.size → Fin d.size
  subset_member : ∀ i,
    a.chart U.index '' (cover.obj i).locus ⊆ Set.range (a.chart (d.index (member i)))

/-- Compact cross intersections and the original net construct a subordinate
full-domain cover of any contained local domain, including an empty one. -/
def subordinateLocalDomainCover [T2Space d.locus] (U : LocalDomain a)
    (hU : U.locus ⊆ d.locus) : d.SubordinateLocalDomainCover U := by
  classical
  let c (i : Fin d.size) := a.compactIntersectionChartCover U.index (d.index i)
    (U.locus ∩ Set.range (a.chart (d.index i)))
    (d.isCompact_localDomain_inter_member U hU i)
    (by
      intro x hx
      rcases hx.1 with ⟨y, hy, rfl⟩
      exact ⟨⟨y, rfl⟩, hx.2⟩)
  let T := (i : Fin d.size) × Fin (c i).size
  let e : Fin (Fintype.card T) ≃ T := (Fintype.equivFin T).symm
  refine {
    cover := {
      size := Fintype.card T
      obj t := U.domain.inter
        (a.restrictionDomain ((c (e t).1).index (e t).2) U.index
          ((c (e t).1).left_subset (e t).2))
      map t := U.domain.interLeft
        (a.restrictionDomain ((c (e t).1).index (e t).2) U.index
          ((c (e t).1).left_subset (e t).2))
      covers := ?_ }
    member t := (e t).1
    subset_member := ?_ }
  · intro x hx
    have hxU : a.chart U.index x ∈ U.locus := ⟨x, hx, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hU hxU)
    obtain ⟨j, hj⟩ := (c i).covers (a.chart U.index x) ⟨hxU, hi⟩
    refine ⟨e.symm ⟨i, j⟩, ?_⟩
    rw [e.apply_symm_apply]
    exact ⟨hx, hj⟩
  · intro t x hx
    rcases hx with ⟨y, hy, rfl⟩
    exact (c (e t).1).right_subset (e t).2 hy.2

namespace SubordinateLocalDomainCover

variable {d} {U : LocalDomain a} (c : d.SubordinateLocalDomainCover U)

/-- Each piece retains its actual presentation in U's original chart. -/
def localDomain (i : Fin c.cover.size) : LocalDomain a :=
  ⟨U.index, c.cover.obj i⟩

/-- The original actual full-domain inclusion is retained as a local-domain arrow. -/
def inclusion (i : Fin c.cover.size) : c.localDomain i ⟶ U :=
  (LocalDomain.sameChartFunctor a U.index).map (c.cover.map i)

@[simp]
theorem inclusion_restriction (i : Fin c.cover.size) :
    (c.inclusion i).restriction = (c.cover.map i).restriction := rfl

theorem localDomain_subset_member (i : Fin c.cover.size) :
    (c.localDomain i).locus ⊆ Set.range (a.chart (d.index (c.member i))) :=
  c.subset_member i

/-- The unchanged covering algebras are full domains over U.algebra and cover
its entire spectrum. The structural maps are the original restrictions. -/
def algebraCover : Domain.FiniteCover (Domain.whole K U.algebra) where
  size := c.cover.size
  obj i := U.domain.relative (c.cover.obj i) (c.cover.map i)
  map i := ⟨(c.cover.map i).restriction, BoundedAlgHom.comp_id _⟩
  covers x _ := by
    obtain ⟨i, hi⟩ := c.cover.covers (U.domain.spectrumMap x)
      (U.domain.represents.hasImageIn x)
    refine ⟨i, ?_⟩
    rw [U.domain.relative_locus_eq_preimage]
    exact hi

@[simp]
theorem algebraCover_obj_algebra (i : Fin c.cover.size) :
    (c.algebraCover.obj i).algebra = (c.localDomain i).algebra := rfl

@[simp]
theorem algebraCover_map_restriction (i : Fin c.cover.size) :
    (c.algebraCover.map i).restriction = (c.inclusion i).restriction := rfl

/-- Every ambient point of U lies in an actual covering local domain. -/
theorem covers (x : X) (hx : x ∈ U.locus) :
    ∃ i, x ∈ (c.localDomain i).locus := by
  rcases hx with ⟨y, hy, rfl⟩
  obtain ⟨i, hi⟩ := c.cover.covers y hy
  exact ⟨i, y, hi, rfl⟩

end SubordinateLocalDomainCover
end Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData
