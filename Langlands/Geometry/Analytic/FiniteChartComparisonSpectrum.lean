import Langlands.Geometry.Analytic.FiniteChartCoverComparison
import Langlands.Geometry.Analytic.FiniteChartGluingSpectrum

/-! # Canonical spectrum maps under finite-chart cover comparisons -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData.ComparisonCover

open Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {d e : FiniteChartGluingData a} (c : d.ComparisonCover e)

/-- The actual continuous inclusion of the target union in the source union. -/
def locusMap : C(e.locus, d.locus) where
  toFun x := ⟨x.val, c.locus_subset x.property⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

@[simp]
theorem locusMap_val (x : e.locus) : (c.locusMap x).val = x.val := rfl

/-- The common-original-chart bounded-map equation gives the exact spectrum
formula on every subordinate chart of a target member. -/
theorem comap_spectrumMap_original (j : Fin e.size) (t : Fin (c.member j).size)
    (z : BanachSpectrum (a.algebra ((c.member j).index t))) :
    BanachSpectrum.comap c.comparison.toBoundedRingHom
        (e.spectrumMap (e.componentMap j
          (BanachSpectrum.comap
            (a.restriction ((c.member j).index t) (e.index j)
              ((c.member j).subset_parent t)).toBoundedRingHom z))) =
      d.spectrumMap (d.componentMap ((c.member j).member t)
        (BanachSpectrum.comap
          (a.restriction ((c.member j).index t) (d.index ((c.member j).member t))
            ((c.member j).subset_member t)).toBoundedRingHom z)) := by
  rw [e.spectrumMap_componentMap, d.spectrumMap_componentMap]
  apply BanachSpectrum.ext
  intro s
  exact congrArg (fun f : BoundedAlgHom K d.SectionAlgebra
    (a.algebra ((c.member j).index t)) => z (f s))
      (c.original_comp_projection_comparison ((c.member j).index t)
        ((c.member j).member t) j ((c.member j).subset_member t)
        ((c.member j).subset_parent t))

/-- The comparison's spectrum pullback agrees with the canonical pointwise
maps on the whole literal union, without any separation assumption. -/
theorem comap_spectrumMap (x : e.locus) :
    BanachSpectrum.comap c.comparison.toBoundedRingHom (e.spectrumMap x) =
      d.spectrumMap (c.locusMap x) := by
  obtain ⟨⟨j, y⟩, rfl⟩ := e.totalMap_surjective x
  obtain ⟨t, ht⟩ := Set.mem_iUnion.mp
    ((c.member j).covers (Set.mem_range_self y))
  obtain ⟨z, hz⟩ := ht
  have hzy : BanachSpectrum.comap
      (a.restriction ((c.member j).index t) (e.index j)
        ((c.member j).subset_parent t)).toBoundedRingHom z = y :=
    (a.isEmbedding_chart (e.index j)).injective
      ((a.restriction_chart _ _ _ z).trans hz)
  have hpoint : c.locusMap (e.componentMap j y) =
      d.componentMap ((c.member j).member t)
        (BanachSpectrum.comap
          (a.restriction ((c.member j).index t) (d.index ((c.member j).member t))
            ((c.member j).subset_member t)).toBoundedRingHom z) := by
    apply Subtype.ext
    exact hz.symm.trans (a.restriction_chart _ _ _ z).symm
  change BanachSpectrum.comap c.comparison.toBoundedRingHom
      (e.spectrumMap (e.componentMap j y)) =
    d.spectrumMap (c.locusMap (e.componentMap j y))
  rw [hpoint, ← hzy]
  exact c.comap_spectrumMap_original j t z

variable (r : e.ComparisonCover d)

/-- Bidirectional cover data identify the literal subspaces with their
unchanged subspace topologies. -/
def locusHomeomorph : e.locus ≃ₜ d.locus :=
  Homeomorph.setCongr (c.locus_eq r).symm

@[simp]
theorem locusHomeomorph_apply (x : e.locus) :
    c.locusHomeomorph r x = c.locusMap x := rfl

/-- The spectrum homeomorphism of the actual bounded equivalence identifies
the two canonical finite-union maps. -/
theorem spectrumHomeomorph_spectrumMap (x : e.locus) :
    (c.algEquiv r).spectrumHomeomorph (e.spectrumMap x) =
      d.spectrumMap (c.locusHomeomorph r x) :=
  c.comap_spectrumMap x

/-- The target pointwise map is transported by the constructed union and
spectrum homeomorphisms. This proves no new affinoid-recognition premise. -/
theorem spectrumMap_eq_transport :
    e.spectrumMap = (c.algEquiv r).spectrumHomeomorph.symm ∘ d.spectrumMap ∘
      c.locusHomeomorph r := by
  funext x
  exact ((c.algEquiv r).spectrumHomeomorph.symm_apply_apply
    (e.spectrumMap x)).symm.trans
      (congrArg (c.algEquiv r).spectrumHomeomorph.symm
        (c.spectrumHomeomorph_spectrumMap r x))

include c r in
/-- Continuity of the canonical map transfers without requiring either
ambient or union Hausdorffness. -/
theorem continuous_spectrumMap_of (h : Continuous d.spectrumMap) :
    Continuous e.spectrumMap := by
  rw [c.spectrumMap_eq_transport r]
  exact ((c.algEquiv r).spectrumHomeomorph.symm.continuous.comp h).comp
    (c.locusHomeomorph r).continuous

include c r in
theorem continuous_spectrumMap_iff :
    Continuous e.spectrumMap ↔ Continuous d.spectrumMap :=
  ⟨r.continuous_spectrumMap_of c, c.continuous_spectrumMap_of r⟩

include c r in
/-- Injectivity transfers by the actual homeomorphism transport formula. -/
theorem injective_spectrumMap_of (h : Function.Injective d.spectrumMap) :
    Function.Injective e.spectrumMap := by
  rw [c.spectrumMap_eq_transport r]
  exact (c.algEquiv r).spectrumHomeomorph.symm.injective.comp
    (h.comp (c.locusHomeomorph r).injective)

include c r in
theorem injective_spectrumMap_iff :
    Function.Injective e.spectrumMap ↔ Function.Injective d.spectrumMap :=
  ⟨r.injective_spectrumMap_of c, c.injective_spectrumMap_of r⟩

include c r in
/-- Surjectivity onto the entire section spectrum also transfers; it is
not inferred merely from the finite original-chart cover. -/
theorem surjective_spectrumMap_of (h : Function.Surjective d.spectrumMap) :
    Function.Surjective e.spectrumMap := by
  rw [c.spectrumMap_eq_transport r]
  exact (c.algEquiv r).spectrumHomeomorph.symm.surjective.comp
    (h.comp (c.locusHomeomorph r).surjective)

include c r in
theorem surjective_spectrumMap_iff :
    Function.Surjective e.spectrumMap ↔ Function.Surjective d.spectrumMap :=
  ⟨r.surjective_spectrumMap_of c, c.surjective_spectrumMap_of r⟩

end Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData.ComparisonCover
