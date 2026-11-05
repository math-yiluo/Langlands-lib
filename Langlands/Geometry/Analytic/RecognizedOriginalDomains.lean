import Langlands.Geometry.Analytic.RecognizedAffinoidCategory
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainFiniteRecognition
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocalization

/-! # Original charts as full domains of recognized affinoid subsets -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

namespace FiniteChartGluingData

variable (d : FiniteChartGluingData a)

/-- Finite subordinate descent identifies the spectrum of the actual
restriction to an original chart with the canonical union point map. -/
theorem comap_originalRestriction [T2Space d.locus] (parent : a.Index)
    (hp : Set.range (a.chart parent) ⊆ d.locus)
    (x : BanachSpectrum (a.algebra parent)) :
    BanachSpectrum.comap (d.originalRestriction parent hp).toBoundedRingHom x =
      d.spectrumMap ⟨a.chart parent x, hp (Set.mem_range_self x)⟩ := by
  let c := d.subordinateCoverOfHausdorff parent hp
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp (c.covers (Set.mem_range_self x))
  obtain ⟨z, hz⟩ := ht
  have hzx : BanachSpectrum.comap
      (a.restriction (c.index t) parent (c.subset_parent t)).toBoundedRingHom z = x :=
    (a.isEmbedding_chart parent).injective ((a.restriction_chart _ _ _ z).trans hz)
  let y := BanachSpectrum.comap
    (a.restriction (c.index t) (d.index (c.member t))
      (c.subset_member t)).toBoundedRingHom z
  have hpoint : d.componentMap (c.member t) y =
      (⟨a.chart parent x, hp (Set.mem_range_self x)⟩ : d.locus) :=
    Subtype.ext ((a.restriction_chart _ _ _ z).trans hz)
  rw [← hpoint, d.spectrumMap_componentMap, ← hzx]
  apply BanachSpectrum.ext
  intro s
  exact congrArg
    (fun q : BoundedAlgHom K d.SectionAlgebra (a.algebra (c.index t)) => z (q s))
    (d.original_comp_originalRestriction parent hp (c.index t)
      (c.subset_parent t) (c.member t) (c.subset_member t))

end FiniteChartGluingData

namespace RecognizedSubset

variable (V : a.RecognizedSubset)

instance : T2Space V.property.cover.locus := V.property.cover_isSpecial.1

/-- Original chart containment determines the actual restriction from
the recognized finite presentation to the unchanged original algebra. -/
def originalRestriction (parent : a.Index) (hp : Set.range (a.chart parent) ⊆ V.locus) :
    BoundedAlgHom K V.algebra (a.algebra parent) :=
  (V.val.gluingData.originalRestriction parent
    (hp.trans V.val.gluingData_locus.symm.subset)).comp
    V.property.algebraEquiv.toBoundedAlgHom

theorem comap_originalRestriction (parent : a.Index)
    (hp : Set.range (a.chart parent) ⊆ V.locus)
    (x : BanachSpectrum (a.algebra parent)) :
    BanachSpectrum.comap (V.originalRestriction parent hp).toBoundedRingHom x =
      V.coordinates ⟨a.chart parent x, hp (Set.mem_range_self x)⟩ := by
  change V.property.algebraEquiv.spectrumHomeomorph
    (BanachSpectrum.comap
      (V.val.gluingData.originalRestriction parent
        (hp.trans V.val.gluingData_locus.symm.subset)).toBoundedRingHom x) = _
  rw [V.val.gluingData.comap_originalRestriction]
  rfl

theorem chart_originalRestriction (parent : a.Index)
    (hp : Set.range (a.chart parent) ⊆ V.locus)
    (x : BanachSpectrum (a.algebra parent)) :
    V.chart (BanachSpectrum.comap (V.originalRestriction parent hp).toBoundedRingHom x) =
      a.chart parent x := by
  rw [V.comap_originalRestriction parent hp x]
  exact congrArg Subtype.val (V.coordinates.symm_apply_apply _)

theorem injective_comap_originalRestriction (parent : a.Index)
    (hp : Set.range (a.chart parent) ⊆ V.locus) :
    Function.Injective
      (BanachSpectrum.comap (V.originalRestriction parent hp).toBoundedRingHom) := by
  intro x y hxy
  apply (a.isEmbedding_chart parent).injective
  exact (V.chart_originalRestriction parent hp x).symm.trans
    ((congrArg V.chart hxy).trans (V.chart_originalRestriction parent hp y))

theorem range_comap_originalRestriction (parent : a.Index)
    (hp : Set.range (a.chart parent) ⊆ V.locus) :
    Set.range (BanachSpectrum.comap (V.originalRestriction parent hp).toBoundedRingHom) =
      V.chart ⁻¹' Set.range (a.chart parent) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (V.chart_originalRestriction parent hp y).symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, V.isEmbedding_chart.injective
      ((V.chart_originalRestriction parent hp y).trans hy)⟩

/-- Passing through the separately witnessed full-domain cover gives the
same entire bounded restriction, by actual comparison naturality. -/
theorem originalRestriction_eq_cover (parent : a.Index)
    (hp : Set.range (a.chart parent) ⊆ V.locus) :
    V.originalRestriction parent hp =
      ((V.property.cover.originalRestriction parent
        (hp.trans V.property.cover_locus.symm.subset)).comp
        (V.val.comparisonEquiv V.property.cover V.property.cover_locus).toBoundedAlgHom).comp
          V.property.algebraEquiv.toBoundedAlgHom := by
  exact (congrArg
    (fun q : BoundedAlgHom K V.val.SectionAlgebra (a.algebra parent) =>
      q.comp V.property.algebraEquiv.toBoundedAlgHom)
    (V.val.gluingData.originalRestriction_comp_restrictionTo V.property.cover
      (V.property.cover_locus.trans V.val.gluingData_locus.symm).subset
      parent (hp.trans V.property.cover_locus.symm.subset))).symm

/-- The actual finite subordinate cover of the original source chart
turns its restriction into a full represented affinoid domain. -/
theorem originalRestriction_represents (parent : a.Index)
    (hp : Set.range (a.chart parent) ⊆ V.locus) :
    Represents K (V.originalRestriction parent hp)
      (Set.range (BanachSpectrum.comap
        (V.originalRestriction parent hp).toBoundedRingHom)) := by
  let d := V.property.cover
  let hp' := hp.trans V.property.cover_locus.symm.subset
  let c := d.subordinateCoverOfHausdorff parent hp'
  apply c.domainCover.represents_of_finiteCover (V.originalRestriction parent hp)
    (V.injective_comap_originalRestriction parent hp)
  intro t
  have heq :
      (c.domainCover.obj t).baseMap.comp (V.originalRestriction parent hp) =
        (a.restriction (c.index t) (d.index (c.member t)) (c.subset_member t)).comp
          (V.property.componentDomain (c.member t)).baseMap := by
    rw [V.originalRestriction_eq_cover parent hp]
    exact congrArg
      (fun q : BoundedAlgHom K d.SectionAlgebra (a.algebra (c.index t)) =>
        (q.comp (V.val.comparisonEquiv d V.property.cover_locus).toBoundedAlgHom).comp
          V.property.algebraEquiv.toBoundedAlgHom)
      (d.original_comp_originalRestriction parent hp' (c.index t)
        (c.subset_parent t) (c.member t) (c.subset_member t))
  rw [heq]
  have hr := (V.property.componentDomain (c.member t)).represents.comp
    (a.restriction_represents (c.index t) (d.index (c.member t)) (c.subset_member t))
  exact hr.2.1.symm ▸ hr

/-- Every contained original chart is now a full domain of the recognized
subset, retaining its unchanged original algebra and actual restriction. -/
def originalDomain (parent : a.Index) (hp : Set.range (a.chart parent) ⊆ V.locus) :
    Domain K V.algebra where
  algebra := a.algebra parent
  baseMap := V.originalRestriction parent hp
  locus := V.chart ⁻¹' Set.range (a.chart parent)
  represents := by
    rw [← V.range_comap_originalRestriction parent hp]
    exact V.originalRestriction_represents parent hp

theorem originalDomain_over_ambient (parent : a.Index)
    (hp : Set.range (a.chart parent) ⊆ V.locus)
    (x : BanachSpectrum (a.algebra parent)) :
    V.chart ((V.originalDomain parent hp).spectrumMap x) = a.chart parent x :=
  V.chart_originalRestriction parent hp x

end RecognizedSubset
end Langlands.Analytic.IndexedAffinoidAtlas
