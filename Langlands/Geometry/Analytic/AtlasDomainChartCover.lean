import Langlands.Geometry.Analytic.AtlasTopology.CompactSubcover
import Langlands.Geometry.Analytic.AtlasAffinoidDomainLocalization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainIntersection
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainTopology

/-! # Actual finite local-domain covers by common original charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- A finite cover of a subset by original charts contained in each of
two specified original chart domains. -/
structure CompactIntersectionChartCover (i j : a.Index) (S : Set X) where
  size : ℕ
  index : Fin size → a.Index
  left_subset : ∀ t, Set.range (a.chart (index t)) ⊆ Set.range (a.chart i)
  right_subset : ∀ t, Set.range (a.chart (index t)) ⊆ Set.range (a.chart j)
  covers : ∀ x ∈ S, ∃ t, x ∈ Set.range (a.chart (index t))

/-- Construct the finite family from compactness and the original net
intersection axiom, without directedness of the original atlas. -/
def compactIntersectionChartCover (i j : a.Index) (S : Set X)
    (hS : IsCompact S)
    (hij : S ⊆ Set.range (a.chart i) ∩ Set.range (a.chart j)) :
    a.CompactIntersectionChartCover i j S := by
  classical
  apply Classical.choice
  obtain ⟨σ, hf, hs, hsub, hcov⟩ :=
    a.isNet_chartFamily.exists_finite_cover_of_subset_inter
      (Set.mem_range_self i) (Set.mem_range_self j) hS hij
  let := hf.fintype
  choose k hk using fun V : σ => hs V.property
  change ∀ V : σ, Set.range (a.chart (k V)) = V.val at hk
  let e := (Fintype.equivFin σ).symm
  refine ⟨⟨Fintype.card σ, fun t => k (e t), ?_, ?_, ?_⟩⟩
  · intro t
    rw [hk]
    exact fun _ hx => (hsub (e t).val (e t).property hx).1
  · intro t
    rw [hk]
    exact fun _ hx => (hsub (e t).val (e t).property hx).2
  · intro x hx
    obtain ⟨V, hV, hxV⟩ := hcov hx
    refine ⟨e.symm ⟨V, hV⟩, ?_⟩
    simpa only [e.apply_symm_apply, hk] using hxV

/-- The compact image of a full local domain has such a common-chart cover
whenever that image is contained in the second original chart. -/
def domainImageChartCover (i j : a.Index) (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart j)) :
    a.CompactIntersectionChartCover i j (a.chart i '' U.locus) :=
  a.compactIntersectionChartCover i j (a.chart i '' U.locus)
    (U.isCompact_locus.image (a.isEmbedding_chart i).continuous)
    (fun _ hx => ⟨by rcases hx with ⟨x, _, rfl⟩; exact ⟨x, rfl⟩, h hx⟩)

namespace CompactIntersectionChartCover

variable {a} {i j : a.Index} {U : Domain K (a.algebra i)}
  (c : a.CompactIntersectionChartCover i j (a.chart i '' U.locus))

/-- Intersect the actual domain with the actual original relative chart
domains. These full intersections and their original quotient projections
give a finite cover in the original domain category. -/
def domainCover : Domain.FiniteCover U where
  size := c.size
  obj t := U.inter (a.restrictionDomain (c.index t) i (c.left_subset t))
  map t := Domain.interLeft U (a.restrictionDomain (c.index t) i (c.left_subset t))
  covers x hx := by
    obtain ⟨t, ht⟩ := c.covers (a.chart i x) ⟨x, hx, rfl⟩
    exact ⟨t, hx, ht⟩

@[simp]
theorem domainCover_obj_locus (t : Fin c.size) :
    (c.domainCover.obj t).locus =
      U.locus ∩ (a.chart i ⁻¹' Set.range (a.chart (c.index t))) := rfl

/-- The second actual quotient projection places each covering member
inside its original relative chart domain. -/
def domainCoverToChart (t : Fin c.size) :
    c.domainCover.obj t ⟶ a.restrictionDomain (c.index t) i (c.left_subset t) :=
  Domain.interRight U (a.restrictionDomain (c.index t) i (c.left_subset t))

/-- Restrict to the common original chart, retaining precisely the actual
intersection algebra and its second bounded quotient projection. -/
def domainOverChart (t : Fin c.size) : Domain K (a.algebra (c.index t)) :=
  a.restrictDomain (c.index t) i (c.left_subset t)
    (c.domainCover.obj t) (c.domainCoverToChart t)

@[simp]
theorem domainOverChart_algebra (t : Fin c.size) :
    (c.domainOverChart t).algebra = (c.domainCover.obj t).algebra := rfl

theorem domainOverChart_comp_restriction (t : Fin c.size) :
    (c.domainOverChart t).baseMap.comp (a.restriction (c.index t) i (c.left_subset t)) =
      (c.domainCover.obj t).baseMap :=
  (c.domainCoverToChart t).comp_baseMap

/-- The same actual intersection algebra is a full domain over the second
original chart by extension from the common original chart. -/
def domainOverRightChart (t : Fin c.size) : Domain K (a.algebra j) :=
  a.extendDomain (c.index t) j (c.right_subset t) (c.domainOverChart t)

@[simp]
theorem domainOverRightChart_algebra (t : Fin c.size) :
    (c.domainOverRightChart t).algebra = (c.domainCover.obj t).algebra := rfl

theorem chart_image_domainOverChart (t : Fin c.size) :
    a.chart (c.index t) '' (c.domainOverChart t).locus =
      a.chart i '' (c.domainCover.obj t).locus := by
  rw [← a.chart_image_extendDomain_locus (c.index t) i (c.left_subset t)
    (c.domainOverChart t)]
  exact congrArg (fun W : Set (BanachSpectrum (a.algebra i)) => a.chart i '' W)
    (a.extend_restrictDomain_locus (c.index t) i (c.left_subset t)
      (c.domainCover.obj t) (c.domainCoverToChart t))

/-- The transported full domain represents exactly the same ambient
subset, including its original intersection with the common chart. -/
theorem chart_image_domainOverRightChart (t : Fin c.size) :
    a.chart j '' (c.domainOverRightChart t).locus =
      a.chart i '' (c.domainCover.obj t).locus :=
  (a.chart_image_extendDomain_locus (c.index t) j (c.right_subset t)
    (c.domainOverChart t)).trans (c.chart_image_domainOverChart t)

theorem chart_image_domainOverRightChart_subset (t : Fin c.size) :
    a.chart j '' (c.domainOverRightChart t).locus ⊆ a.chart i '' U.locus := by
  rw [c.chart_image_domainOverRightChart]
  exact Set.image_mono (c.domainCover.map t).subset

end CompactIntersectionChartCover

/-- The constructed actual finite full-domain cover for any local domain
contained in another original chart. -/
def localDomainChartCover (i j : a.Index) (U : Domain K (a.algebra i))
    (h : a.chart i '' U.locus ⊆ Set.range (a.chart j)) : Domain.FiniteCover U :=
  (a.domainImageChartCover i j U h).domainCover

end Langlands.Analytic.IndexedAffinoidAtlas
