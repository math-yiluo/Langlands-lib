import Langlands.Geometry.Analytic.SaturatedAtlasDomainClosure
import Langlands.Geometry.Analytic.StrongAtlasQuasiIsomorphisms
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainCoverRefinement

/-! # Original-chart refinements of full-domain covers -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

namespace HasAllLocalDomains

variable (ha : a.HasAllLocalDomains)

/-- Choose an original chart for the entire ambient image of a full domain.
The hypothesis is proved for the actual constructed saturated atlas. -/
def domainChartIndex (i : a.Index) (U : Domain K (a.algebra i)) : a.Index :=
  (ha.exists_chart ⟨i, U⟩).choose

theorem range_domainChartIndex (i : a.Index) (U : Domain K (a.algebra i)) :
    Set.range (a.chart (ha.domainChartIndex i U)) = a.chart i '' U.locus :=
  (ha.exists_chart ⟨i, U⟩).choose_spec

theorem domainChartIndex_subset (i : a.Index) (U : Domain K (a.algebra i)) :
    Set.range (a.chart (ha.domainChartIndex i U)) ⊆ Set.range (a.chart i) := by
  rw [ha.range_domainChartIndex]
  exact Set.image_subset_range _ _

/-- This full-domain presentation uses exactly the original chart algebra and
the original bounded restriction to the containing chart. -/
def chartDomain (i : a.Index) (U : Domain K (a.algebra i)) :
    Domain K (a.algebra i) :=
  a.restrictionDomain (ha.domainChartIndex i U) i (ha.domainChartIndex_subset i U)

@[simp]
theorem chartDomain_algebra (i : a.Index) (U : Domain K (a.algebra i)) :
    (ha.chartDomain i U).algebra = a.algebra (ha.domainChartIndex i U) := rfl

@[simp]
theorem chartDomain_baseMap (i : a.Index) (U : Domain K (a.algebra i)) :
    (ha.chartDomain i U).baseMap =
      a.restriction (ha.domainChartIndex i U) i (ha.domainChartIndex_subset i U) := rfl

/-- Equality holds in the original containing spectrum, before taking any
images or passing to an isomorphism class. -/
theorem chartDomain_locus (i : a.Index) (U : Domain K (a.algebra i)) :
    (ha.chartDomain i U).locus = U.locus := by
  change a.chart i ⁻¹' Set.range (a.chart (ha.domainChartIndex i U)) = U.locus
  rw [ha.range_domainChartIndex]
  exact Set.preimage_image_eq _ (a.isEmbedding_chart i).injective

/-- The full universal properties construct both actual bounded comparison
maps over the original algebra, without identifying maps from their spectra. -/
def chartDomainIso (i : a.Index) (U : Domain K (a.algebra i)) :
    U ≅ ha.chartDomain i U :=
  Domain.isoOfLocusEq U _ (ha.chartDomain_locus i U).symm

theorem chartDomainIso_hom_comp_baseMap (i : a.Index)
    (U : Domain K (a.algebra i)) :
    (ha.chartDomainIso i U).hom.restriction.comp
        (a.restriction (ha.domainChartIndex i U) i (ha.domainChartIndex_subset i U)) =
      U.baseMap :=
  (ha.chartDomainIso i U).hom.comp_baseMap

theorem chartDomainIso_inv_comp_baseMap (i : a.Index)
    (U : Domain K (a.algebra i)) :
    (ha.chartDomainIso i U).inv.restriction.comp U.baseMap =
      a.restriction (ha.domainChartIndex i U) i (ha.domainChartIndex_subset i U) :=
  (ha.chartDomainIso i U).inv.comp_baseMap

/-- Retain the same finite index, replacing each domain presentation by an
original chart and transporting its actual arrow by the bounded comparison. -/
def chartCover {i : a.Index} {U : Domain K (a.algebra i)}
    (c : Domain.FiniteCover U) : Domain.FiniteCover U where
  size := c.size
  obj t := ha.chartDomain i (c.obj t)
  map t := (ha.chartDomainIso i (c.obj t)).inv ≫ c.map t
  covers x hx := by
    obtain ⟨t, ht⟩ := c.covers x hx
    exact ⟨t, (ha.chartDomain_locus i (c.obj t)).symm ▸ ht⟩

@[simp]
theorem chartCover_size {i : a.Index} {U : Domain K (a.algebra i)}
    (c : Domain.FiniteCover U) : (ha.chartCover c).size = c.size := rfl

@[simp]
theorem chartCover_obj_algebra {i : a.Index} {U : Domain K (a.algebra i)}
    (c : Domain.FiniteCover U) (t : Fin c.size) :
    ((ha.chartCover c).obj t).algebra =
      a.algebra (ha.domainChartIndex i (c.obj t)) := rfl

theorem chartCover_obj_locus {i : a.Index} {U : Domain K (a.algebra i)}
    (c : Domain.FiniteCover U) (t : Fin c.size) :
    ((ha.chartCover c).obj t).locus = (c.obj t).locus :=
  ha.chartDomain_locus i (c.obj t)

/-- Every new component retains its complete bounded map from the covered
domain's algebra, expressed using the original comparison and arrow. -/
theorem chartCover_map_restriction {i : a.Index} {U : Domain K (a.algebra i)}
    (c : Domain.FiniteCover U) (t : Fin c.size) :
    ((ha.chartCover c).map t).restriction =
      (ha.chartDomainIso i (c.obj t)).inv.restriction.comp (c.map t).restriction := rfl

def chartCoverRefinement {i : a.Index} {U : Domain K (a.algebra i)}
    (c : Domain.FiniteCover U) : Domain.FiniteCover.Refinement (ha.chartCover c) c where
  index t := t
  map t := (ha.chartDomainIso i (c.obj t)).inv

def chartCoverInverseRefinement {i : a.Index} {U : Domain K (a.algebra i)}
    (c : Domain.FiniteCover U) : Domain.FiniteCover.Refinement c (ha.chartCover c) where
  index t := t
  map t := (ha.chartDomainIso i (c.obj t)).hom

/-- Both componentwise inverse maps retain the original finite cover up to an
actual isomorphism in its refinement category. -/
def chartCoverIso {i : a.Index} {U : Domain K (a.algebra i)}
    (c : Domain.FiniteCover U) : ha.chartCover c ≅ c where
  hom := ha.chartCoverRefinement c
  inv := ha.chartCoverInverseRefinement c
  hom_inv_id := Domain.FiniteCover.Refinement.ext rfl
  inv_hom_id := Domain.FiniteCover.Refinement.ext rfl

theorem chartDomainIso_hom_chartCover_map {i : a.Index}
    {U : Domain K (a.algebra i)} (c : Domain.FiniteCover U) (t : Fin c.size) :
    (ha.chartDomainIso i (c.obj t)).hom ≫ (ha.chartCover c).map t = c.map t :=
  @Subsingleton.elim (Domain.Inclusion (c.obj t) U) inferInstance _ _

/-- The original-chart images themselves cover exactly the covered ambient
domain, including the empty-cover case. -/
theorem chartCover_ambient_coverage {i : a.Index} {U : Domain K (a.algebra i)}
    (c : Domain.FiniteCover U) :
    (⋃ t : Fin c.size, Set.range (a.chart (ha.domainChartIndex i (c.obj t)))) =
      a.chart i '' U.locus := by
  ext x
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨t, ht⟩
    rw [ha.range_domainChartIndex] at ht
    exact Set.image_mono (c.map t).subset ht
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨t, ht⟩ := c.covers y hy
    exact ⟨t, (ha.range_domainChartIndex i (c.obj t)).symm ▸ ⟨y, ht, rfl⟩⟩

end HasAllLocalDomains
end Langlands.Analytic.IndexedAffinoidAtlas
