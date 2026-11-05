import Langlands.Geometry.Analytic.FiniteChartGluingAlgebra
import Mathlib.Topology.ContinuousMap.Basic

/-! # The actual finite-union map to its Banach section spectrum -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData

open Set Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  (d : FiniteChartGluingData a)

instance compactSpace_locus : CompactSpace d.locus :=
  isCompact_iff_compactSpace.mp d.isCompact_locus

/-- Each original chart lands in the literal subspace union. -/
def componentMap (i : Fin d.size) :
    C(BanachSpectrum (a.algebra (d.index i)), d.locus) where
  toFun x := ⟨a.chart (d.index i) x, Set.mem_iUnion.mpr ⟨i, x, rfl⟩⟩
  continuous_toFun := (a.isEmbedding_chart (d.index i)).continuous.subtype_mk _

@[simp]
theorem componentMap_val (i : Fin d.size)
    (x : BanachSpectrum (a.algebra (d.index i))) :
    (d.componentMap i x).val = a.chart (d.index i) x := rfl

/-- The actual finite disjoint union of the original spectra covers the
literal ambient union, with its existing subspace topology. -/
def totalMap : C((Σ i : Fin d.size, BanachSpectrum (a.algebra (d.index i))), d.locus) where
  toFun x := d.componentMap x.1 x.2
  continuous_toFun := continuous_sigma fun i => (d.componentMap i).continuous

theorem totalMap_surjective : Function.Surjective d.totalMap := by
  intro x
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp x.property
  exact ⟨⟨i, y⟩, Subtype.ext hy⟩

/-- The local continuous spectrum maps assembled before descent. -/
def spectrumFamilyMap :
    C((Σ i : Fin d.size, BanachSpectrum (a.algebra (d.index i))),
      BanachSpectrum d.SectionAlgebra) where
  toFun x := d.chartSpectrumMap x.1 x.2
  continuous_toFun := continuous_sigma fun i => (d.chartSpectrumMap i).continuous

theorem spectrumFamilyMap_factorsThrough :
    Function.FactorsThrough d.spectrumFamilyMap d.totalMap := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  exact d.chartSpectrumMap_eq_of_chart_eq i j x y
    (congrArg (fun z : d.locus => z.val) h)

/-- The actual pointwise map to the constructed Banach equalizer's spectrum.
Fiber agreement makes it independent of the chosen chart representative.
It is defined even before continuity of the finite cover is established. -/
def spectrumMap (x : d.locus) : BanachSpectrum d.SectionAlgebra :=
  d.spectrumFamilyMap (Function.surjInv d.totalMap_surjective x)

@[simp]
theorem spectrumMap_componentMap (i : Fin d.size)
    (x : BanachSpectrum (a.algebra (d.index i))) :
    d.spectrumMap (d.componentMap i x) = d.chartSpectrumMap i x := by
  change d.spectrumFamilyMap
    (Function.surjInv d.totalMap_surjective (d.componentMap i x)) =
      d.spectrumFamilyMap ⟨i, x⟩
  apply d.spectrumFamilyMap_factorsThrough
  exact Function.surjInv_eq d.totalMap_surjective (d.componentMap i x)

theorem spectrumMap_comp_totalMap : d.spectrumMap ∘ d.totalMap = d.spectrumFamilyMap := by
  funext x
  exact d.spectrumMap_componentMap x.1 x.2

/-- The pointwise map is characterized by all actual original charts,
without a separation hypothesis on the union. -/
theorem spectrumMap_unique (f : d.locus → BanachSpectrum d.SectionAlgebra)
    (hf : ∀ i x, f (d.componentMap i x) = d.chartSpectrumMap i x) :
    f = d.spectrumMap := by
  funext x
  obtain ⟨⟨i, y⟩, rfl⟩ := d.totalMap_surjective x
  exact (hf i y).trans (d.spectrumMap_componentMap i y).symm

/-- The exact additional topological fact needed for continuity of the
constructed pointwise map. No output affine algebra is involved. -/
theorem continuous_spectrumMap_of_isQuotientMap (h : IsQuotientMap d.totalMap) :
    Continuous d.spectrumMap := by
  apply h.continuous_iff.mpr
  rw [d.spectrumMap_comp_totalMap]
  exact d.spectrumFamilyMap.continuous

/-- For a Hausdorff union the finite compact cover is automatically closed. -/
theorem totalMap_isClosedMap [T2Space d.locus] : IsClosedMap d.totalMap :=
  d.totalMap.continuous.isClosedMap

theorem totalMap_isQuotientMap [T2Space d.locus] : IsQuotientMap d.totalMap :=
  .of_surjective_continuous d.totalMap_surjective d.totalMap.continuous

/-- The finite compact cover of a Hausdorff literal union detects continuity. -/
theorem continuous_iff [T2Space d.locus] {Y : Type z} [TopologicalSpace Y]
    (f : d.locus → Y) :
    Continuous f ↔ ∀ i, Continuous (f ∘ d.componentMap i) :=
  d.totalMap_isQuotientMap.continuous_iff.trans continuous_sigma_iff

theorem continuous_spectrumMap [T2Space d.locus] : Continuous d.spectrumMap :=
  d.continuous_spectrumMap_of_isQuotientMap d.totalMap_isQuotientMap

/-- The continuous realization of the already constructed pointwise map.
The Hausdorff assumption is on this union alone, not on the ambient space. -/
def spectrumMapContinuous [T2Space d.locus] :
    C(d.locus, BanachSpectrum d.SectionAlgebra) :=
  ⟨d.spectrumMap, d.continuous_spectrumMap⟩

@[simp]
theorem spectrumMapContinuous_componentMap [T2Space d.locus] (i : Fin d.size) :
    d.spectrumMapContinuous.comp (d.componentMap i) = d.chartSpectrumMap i :=
  ContinuousMap.ext (d.spectrumMap_componentMap i)

/-- The image is exactly the finite union of the original local spectrum
images. This set equality does not require continuity or Hausdorffness. -/
theorem range_spectrumMap : Set.range d.spectrumMap =
    ⋃ i, Set.range (d.chartSpectrumMap i) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨⟨i, z⟩, rfl⟩ := d.totalMap_surjective x
    exact Set.mem_iUnion.mpr ⟨i, z, (d.spectrumMap_componentMap i z).symm⟩
  · intro hy
    obtain ⟨i, z, rfl⟩ := Set.mem_iUnion.mp hy
    exact ⟨d.componentMap i z, d.spectrumMap_componentMap i z⟩

/-- Compactness of the local images proves compactness of the global
image even before the continuity criterion has been discharged. -/
theorem isCompact_range_spectrumMap : IsCompact (Set.range d.spectrumMap) := by
  rw [d.range_spectrumMap]
  exact isCompact_iUnion fun i => isCompact_range (d.chartSpectrumMap i).continuous

theorem isClosed_range_spectrumMap : IsClosed (Set.range d.spectrumMap) :=
  d.isCompact_range_spectrumMap.isClosed

/-- Original section evaluation on every chart is exactly the associated
coordinate seminorm, on the original quotient carrier. -/
theorem spectrumMap_componentMap_apply (i : Fin d.size)
    (x : BanachSpectrum (a.algebra (d.index i))) (s : d.SectionAlgebra) :
    d.spectrumMap (d.componentMap i x) s = x (d.projection i s) := by
  rw [d.spectrumMap_componentMap]
  rfl

variable {S : Type z} [NormedCommRing S] [Algebra K S]

/-- Any bounded test-algebra map into the equalizer retains its full local
coordinate formula after passing to spectra. -/
theorem comap_spectrumMap_componentMap (f : BoundedAlgHom K S d.SectionAlgebra)
    (i : Fin d.size) (x : BanachSpectrum (a.algebra (d.index i))) :
    BanachSpectrum.comap f.toBoundedRingHom (d.spectrumMap (d.componentMap i x)) =
      BanachSpectrum.comap ((d.projection i).comp f).toBoundedRingHom x := by
  rw [d.spectrumMap_componentMap]
  rfl

end Langlands.Analytic.IndexedAffinoidAtlas.FiniteChartGluingData
