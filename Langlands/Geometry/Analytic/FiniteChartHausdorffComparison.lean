import Langlands.Geometry.Analytic.FiniteChartSubordinateCover
import Langlands.Geometry.Analytic.FiniteChartComparisonSpectrum

/-! # Canonical section restrictions for Hausdorff finite unions -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData

open Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  (d e : FiniteChartGluingData a)

/-- A contained literal union inherits Hausdorffness from the containing
union, without any separation assumption on the ambient space. -/
theorem t2Space_locus_of_subset [T2Space d.locus] (h : e.locus ⊆ d.locus) :
    T2Space e.locus :=
  (Topology.IsEmbedding.inclusion h).t2Space

/-- Construct all member and overlap covers from literal inclusion alone
when the containing union is Hausdorff. -/
def comparisonCoverOfHausdorff [T2Space d.locus] (h : e.locus ⊆ d.locus) :
    d.ComparisonCover e where
  member i := d.subordinateCoverOfHausdorff (e.index i)
    (fun _ hx => h (Set.mem_iUnion.mpr ⟨i, hx⟩))
  overlap i j := d.subordinateCoverOfHausdorff (e.overlap i j)
    (fun _ hx => h (Set.mem_iUnion.mpr ⟨i, e.overlap_subset_left i j hx⟩))

/-- The actual bounded restriction to a contained finite union. Its
subordinate original-chart covers are constructed, not supplied. -/
def restrictionTo [T2Space d.locus] (h : e.locus ⊆ d.locus) :
    BoundedAlgHom K d.SectionAlgebra e.SectionAlgebra :=
  (d.comparisonCoverOfHausdorff e h).comparison

@[simp]
theorem projection_comp_restrictionTo [T2Space d.locus]
    (h : e.locus ⊆ d.locus) (i : Fin e.size) :
    (e.projection i).comp (d.restrictionTo e h) =
      d.originalRestriction (e.index i)
        (fun _ hx => h (Set.mem_iUnion.mpr ⟨i, hx⟩)) := rfl

/-- Every other geometric comparison-cover choice gives the same full
bounded restriction. -/
theorem restrictionTo_eq_comparison [T2Space d.locus]
    (h : e.locus ⊆ d.locus) (c : d.ComparisonCover e) :
    d.restrictionTo e h = c.comparison :=
  (d.comparisonCoverOfHausdorff e h).comparison_eq c

/-- The constructed original restriction recovers a defining projection. -/
theorem originalRestriction_index [T2Space d.locus] (i : Fin d.size)
    (hi : Set.range (a.chart (d.index i)) ⊆ d.locus) :
    d.originalRestriction (d.index i) hi = d.projection i := by
  have h := (d.subordinateCoverOfHausdorff (d.index i) hi).restriction_of_member
    i Subset.rfl
  simpa only [originalRestriction, a.restriction_id, BoundedAlgHom.id_comp] using h

@[simp]
theorem restrictionTo_self [T2Space d.locus] :
    d.restrictionTo d Subset.rfl = BoundedAlgHom.id K d.SectionAlgebra := by
  apply d.hom_ext
  intro i
  exact (d.projection_comp_restrictionTo d Subset.rfl i).trans
    ((d.originalRestriction_index i _).trans (BoundedAlgHom.comp_id _).symm)

/-- Restricting first to a contained union and then to an original chart
equals the directly constructed restriction to that original chart. -/
theorem originalRestriction_comp_restrictionTo [T2Space d.locus] [T2Space e.locus]
    (h : e.locus ⊆ d.locus) (parent : a.Index)
    (hp : Set.range (a.chart parent) ⊆ e.locus) :
    (e.originalRestriction parent hp).comp (d.restrictionTo e h) =
      d.originalRestriction parent (hp.trans h) := by
  let c := e.subordinateCoverOfHausdorff parent hp
  apply BoundedAlgHom.ext
  intro s
  apply c.domainCover.algebra_ext_of_restrict_eq
  intro t
  have he := e.original_comp_originalRestriction parent hp (c.index t)
    (c.subset_parent t) (c.member t) (c.subset_member t)
  have he' := congrArg
    (fun f : BoundedAlgHom K e.SectionAlgebra (a.algebra (c.index t)) =>
      f.comp (d.restrictionTo e h)) he
  have hd := d.originalRestriction_naturality (e.index (c.member t)) (c.index t)
    (fun _ hx => h (Set.mem_iUnion.mpr ⟨c.member t, hx⟩))
    ((c.subset_parent t).trans (hp.trans h)) (c.subset_member t)
  have hp' := d.originalRestriction_naturality parent (c.index t)
    (hp.trans h) ((c.subset_parent t).trans (hp.trans h)) (c.subset_parent t)
  have hm := congrArg
    (fun f : BoundedAlgHom K d.SectionAlgebra (a.algebra (e.index (c.member t))) =>
      (a.restriction (c.index t) (e.index (c.member t)) (c.subset_member t)).comp f)
    (d.projection_comp_restrictionTo e h (c.member t))
  exact congrArg
    (fun f : BoundedAlgHom K d.SectionAlgebra (a.algebra (c.index t)) => f s)
    (((he'.trans hm).trans hd).trans hp'.symm)

/-- The actual bounded maps satisfy composition for nested literal unions. -/
theorem restrictionTo_comp [T2Space d.locus] [T2Space e.locus]
    (f : FiniteChartGluingData a)
    (h : e.locus ⊆ d.locus) (k : f.locus ⊆ e.locus) :
    (e.restrictionTo f k).comp (d.restrictionTo e h) =
      d.restrictionTo f (k.trans h) := by
  apply f.hom_ext
  intro i
  have he := congrArg
    (fun q : BoundedAlgHom K e.SectionAlgebra (a.algebra (f.index i)) =>
      q.comp (d.restrictionTo e h))
    (e.projection_comp_restrictionTo f k i)
  exact (he.trans (d.originalRestriction_comp_restrictionTo e h (f.index i)
    (fun _ hx => k (Set.mem_iUnion.mpr ⟨i, hx⟩)))).trans
      (d.projection_comp_restrictionTo f (k.trans h) i).symm

/-- The canonical point maps commute with the constructed restriction and
the literal subspace inclusion on every point of the contained union. -/
theorem comap_spectrumMap_restrictionTo [T2Space d.locus]
    (h : e.locus ⊆ d.locus) (x : e.locus) :
    BanachSpectrum.comap (d.restrictionTo e h).toBoundedRingHom (e.spectrumMap x) =
      d.spectrumMap ⟨x.val, h x.property⟩ :=
  (d.comparisonCoverOfHausdorff e h).comap_spectrumMap x

/-- Equal literal Hausdorff unions have actually constructed bounded
equivalent section algebras. Only the source union's Hausdorffness is input. -/
def sectionAlgEquivOfLocusEq [T2Space d.locus] (h : d.locus = e.locus) :
    BoundedAlgEquiv K d.SectionAlgebra e.SectionAlgebra := by
  letI : T2Space e.locus := (Homeomorph.setCongr h).t2Space
  exact (d.comparisonCoverOfHausdorff e h.symm.subset).algEquiv
    (e.comparisonCoverOfHausdorff d h.subset)

@[simp]
theorem sectionAlgEquivOfLocusEq_toBoundedAlgHom [T2Space d.locus]
    (h : d.locus = e.locus) :
    (d.sectionAlgEquivOfLocusEq e h).toBoundedAlgHom =
      d.restrictionTo e h.symm.subset := rfl

/-- The contravariant spectrum homeomorphism identifies the two canonical
point maps over the unchanged ambient points. -/
theorem sectionAlgEquivOfLocusEq_spectrumMap [T2Space d.locus]
    (h : d.locus = e.locus) (x : e.locus) :
    (d.sectionAlgEquivOfLocusEq e h).spectrumHomeomorph (e.spectrumMap x) =
      d.spectrumMap (Homeomorph.setCongr h.symm x) :=
  d.comap_spectrumMap_restrictionTo e h.symm.subset x

/-- The complete target point map is transported by the actual algebra
equivalence and the identity on the literal subspaces. -/
theorem spectrumMap_eq_transportOfLocusEq [T2Space d.locus]
    (h : d.locus = e.locus) :
    e.spectrumMap = (d.sectionAlgEquivOfLocusEq e h).spectrumHomeomorph.symm ∘
      d.spectrumMap ∘ Homeomorph.setCongr h.symm := by
  let : T2Space e.locus := (Homeomorph.setCongr h).t2Space
  exact (d.comparisonCoverOfHausdorff e h.symm.subset).spectrumMap_eq_transport
    (e.comparisonCoverOfHausdorff d h.subset)

/-- Injectivity is independent of the defining family; this transports
recognition data without assuming or proving it for arbitrary unions. -/
theorem injective_spectrumMap_iff_of_locus_eq [T2Space d.locus]
    (h : d.locus = e.locus) :
    Function.Injective e.spectrumMap ↔ Function.Injective d.spectrumMap := by
  let : T2Space e.locus := (Homeomorph.setCongr h).t2Space
  exact (d.comparisonCoverOfHausdorff e h.symm.subset).injective_spectrumMap_iff
    (e.comparisonCoverOfHausdorff d h.subset)

/-- Surjectivity onto the whole Banach spectrum is likewise independent of
the defining family, and remains a separate recognition condition. -/
theorem surjective_spectrumMap_iff_of_locus_eq [T2Space d.locus]
    (h : d.locus = e.locus) :
    Function.Surjective e.spectrumMap ↔ Function.Surjective d.spectrumMap := by
  let : T2Space e.locus := (Homeomorph.setCongr h).t2Space
  exact (d.comparisonCoverOfHausdorff e h.symm.subset).surjective_spectrumMap_iff
    (e.comparisonCoverOfHausdorff d h.subset)

end Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData
