import Langlands.Geometry.Analytic.AffinoidRealizationSpecialCover

/-! # Recognition from an algebraic parent of a finite chart cover -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData

open Set Topology PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  (d : FiniteChartGluingData a)

/-- Algebraic parent data: full component domains cover the parent spectrum
and their exact spectral intersections are the actual chart overlaps.
No parent chart, embedding or section-algebra equivalence is supplied. -/
structure ParentData where
  algebra : PresentedAffinoidAlgebra K
  restriction : ∀ i : Fin d.size, BoundedAlgHom K algebra (a.algebra (d.index i))
  represents : ∀ i, Represents K (restriction i)
    (range (BanachSpectrum.comap (restriction i).toBoundedRingHom))
  compatible : d.MapCompatible restriction
  covers : ∀ x : BanachSpectrum algebra,
    ∃ i, x ∈ range (BanachSpectrum.comap (restriction i).toBoundedRingHom)
  overlap_range : ∀ i j,
    range (BanachSpectrum.comap ((d.leftRestriction i j).comp (restriction i)).toBoundedRingHom) =
      range (BanachSpectrum.comap (restriction i).toBoundedRingHom) ∩
        range (BanachSpectrum.comap (restriction j).toBoundedRingHom)

/-- A Hausdorff containing patch gives precisely the separation needed
on this finite union, with no ambient separation hypothesis. -/
theorem t2Space_locus_of_hausdorff_container (O : Set X) [T2Space O] (hO : d.locus ⊆ O) :
    T2Space d.locus :=
  (IsEmbedding.subtypeVal.codRestrict O (fun x : d.locus => hO x.property)).t2Space

namespace ParentData

variable {d} (c : d.ParentData)

/-- Each original component is a full domain of the actual supplied parent. -/
def componentDomain (i : Fin d.size) : Domain K c.algebra where
  algebra := a.algebra (d.index i)
  baseMap := c.restriction i
  locus := range (BanachSpectrum.comap (c.restriction i).toBoundedRingHom)
  represents := c.represents i

variable [T2Space d.locus]

/-- The canonical equalizer point map followed by the entire bounded
parent-to-equalizer map. This constructs the global map, rather than
assuming a parent spectrum realization. -/
def spectrumMap : C(d.locus, BanachSpectrum c.algebra) :=
  (BanachSpectrum.comapContinuous (d.lift c.restriction c.compatible).toBoundedRingHom).comp
    d.spectrumMapContinuous

@[simp]
theorem spectrumMap_componentMap (i : Fin d.size)
    (x : BanachSpectrum (a.algebra (d.index i))) :
    c.spectrumMap (d.componentMap i x) =
      BanachSpectrum.comap (c.restriction i).toBoundedRingHom x := by
  change BanachSpectrum.comap (d.lift c.restriction c.compatible).toBoundedRingHom
    (d.spectrumMap (d.componentMap i x)) = _
  rw [d.spectrumMap_componentMap]
  rfl

theorem spectrumMap_surjective : Function.Surjective c.spectrumMap := by
  intro x
  obtain ⟨i, y, hy⟩ := c.covers x
  exact ⟨d.componentMap i y, (c.spectrumMap_componentMap i y).trans hy⟩

/-- Exact full-domain overlaps prevent identifications of distinct parent
points in different component charts. Full bounded compatibility is used
before passing to the corresponding spectrum identity. -/
theorem spectrumMap_injective : Function.Injective c.spectrumMap := by
  intro x y hxy
  obtain ⟨⟨i, s⟩, rfl⟩ := d.totalMap_surjective x
  obtain ⟨⟨j, t⟩, rfl⟩ := d.totalMap_surjective y
  change c.spectrumMap (d.componentMap i s) = c.spectrumMap (d.componentMap j t) at hxy
  rw [c.spectrumMap_componentMap, c.spectrumMap_componentMap] at hxy
  obtain ⟨z, hz⟩ : BanachSpectrum.comap (c.restriction i).toBoundedRingHom s ∈
      range (BanachSpectrum.comap
        ((d.leftRestriction i j).comp (c.restriction i)).toBoundedRingHom) := by
    rw [c.overlap_range]
    exact ⟨⟨s, rfl⟩, ⟨t, hxy.symm⟩⟩
  have hs : BanachSpectrum.comap (d.leftRestriction i j).toBoundedRingHom z = s := by
    apply (c.componentDomain i).spectrumMap_injective
    exact hz
  have ht : BanachSpectrum.comap (d.rightRestriction i j).toBoundedRingHom z = t := by
    apply (c.componentDomain j).spectrumMap_injective
    change BanachSpectrum.comap
      ((d.rightRestriction i j).comp (c.restriction j)).toBoundedRingHom z = _
    rw [← c.compatible i j]
    exact hz.trans hxy
  apply Subtype.ext
  change a.chart (d.index i) s = a.chart (d.index j) t
  rw [← hs, ← ht]
  exact (a.restriction_chart _ _ _ z).trans (a.restriction_chart _ _ _ z).symm

/-- The actual finite union and the parent spectrum are homeomorphic,
by their constructed continuous bijection and compactness of the union. -/
def spectrumHomeomorph : d.locus ≃ₜ BanachSpectrum c.algebra :=
  (Equiv.ofBijective c.spectrumMap
    ⟨c.spectrumMap_injective, c.spectrumMap_surjective⟩).toHomeomorphOfContinuousClosed
      c.spectrumMap.continuous c.spectrumMap.continuous.isClosedMap

@[simp]
theorem spectrumHomeomorph_componentMap (i : Fin d.size)
    (x : BanachSpectrum (a.algebra (d.index i))) :
    c.spectrumHomeomorph (d.componentMap i x) =
      BanachSpectrum.comap (c.restriction i).toBoundedRingHom x :=
  c.spectrumMap_componentMap i x

/-- The actual embedded parent chart is constructed by inverting the
proved homeomorphism onto the literal finite union. -/
def chart : C(BanachSpectrum c.algebra, X) :=
  ⟨fun x => (c.spectrumHomeomorph.symm x).val,
    continuous_subtype_val.comp c.spectrumHomeomorph.symm.continuous⟩

theorem isEmbedding_chart : IsEmbedding c.chart :=
  IsEmbedding.subtypeVal.comp c.spectrumHomeomorph.symm.isEmbedding

theorem range_chart : range c.chart = d.locus := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact (c.spectrumHomeomorph.symm y).property
  · intro hx
    exact ⟨c.spectrumHomeomorph ⟨x, hx⟩,
      congrArg Subtype.val (c.spectrumHomeomorph.symm_apply_apply ⟨x, hx⟩)⟩

theorem chart_component (i : Fin d.size)
    (x : BanachSpectrum (a.algebra (d.index i))) :
    c.chart (BanachSpectrum.comap (c.restriction i).toBoundedRingHom x) =
      a.chart (d.index i) x := by
  have h := congrArg Subtype.val (c.spectrumHomeomorph.symm_apply_apply (d.componentMap i x))
  rw [c.spectrumHomeomorph_componentMap] at h
  exact h

theorem range_comap_restriction (i : Fin d.size) :
    range (BanachSpectrum.comap (c.restriction i).toBoundedRingHom) =
      c.chart ⁻¹' range (a.chart (d.index i)) := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y, (c.chart_component i y).symm⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, c.isEmbedding_chart.injective ((c.chart_component i y).trans hy)⟩

/-- All actual finite affinoid realization data are recovered from the
algebraic parent and its full finite overlap data. -/
def affinoidRealization : d.AffinoidRealization where
  algebra := c.algebra
  chart := c.chart
  isEmbedding_chart := c.isEmbedding_chart
  range_chart := c.range_chart
  restriction := c.restriction
  restriction_chart := c.chart_component
  represents i := (c.range_comap_restriction i) ▸ c.represents i
  compatible := c.compatible

/-- The proved actual realization makes the literal finite union special
and supplies all intrinsic full recognition conditions. -/
def recognizedSubset : a.RecognizedSubset := c.affinoidRealization.recognizedSubset

@[simp]
theorem recognizedSubset_locus : c.recognizedSubset.locus = d.locus := rfl

/-- The entire supplied parent algebra is boundedly equivalent to the
canonical recognized algebra, including nonreduced coefficients. -/
def recognitionEquiv : BoundedAlgEquiv K c.algebra c.recognizedSubset.algebra :=
  c.affinoidRealization.recognitionEquiv

theorem recognizedSubset_chart (x : BanachSpectrum c.recognizedSubset.algebra) :
    c.recognizedSubset.chart x = c.chart (c.recognitionEquiv.spectrumHomeomorph x) :=
  c.affinoidRealization.recognizedSubset_chart x

end ParentData

end Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData
