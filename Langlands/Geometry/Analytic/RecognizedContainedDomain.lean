import Langlands.Geometry.Analytic.FullRecognitionPairSystems

/-! # Recognized affinoid subsets inside an original chart -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.RecognizedSubset

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  (W : a.RecognizedSubset) (j : a.Index) (hW : W.locus ⊆ Set.range (a.chart j))

/-- All original restrictions to charts contained in the recognized subset. -/
def containedChartPullbacks :
    ∀ k : a.Index, Set.range (a.chart k) ⊆ W.locus →
      BoundedAlgHom K (a.algebra j) (a.algebra k) :=
  fun k hk => a.restriction k j (hk.trans hW)

theorem containedChartPullbacks_compatible :
    W.IsChartCompatible (W.containedChartPullbacks j hW) := by
  intro k l hk hl hkl
  exact (a.restriction_comp k l j hkl (hl.trans hW) (hk.trans hW)).symm

/-- The complete original-chart map is obtained by bounded descent. -/
def containedRestriction : BoundedAlgHom K (a.algebra j) W.algebra :=
  W.glue (W.containedChartPullbacks j hW) (W.containedChartPullbacks_compatible j hW)

/-- The map restricts to the unchanged bounded map on every contained chart. -/
theorem originalRestriction_comp_containedRestriction
    (k : a.Index) (hk : Set.range (a.chart k) ⊆ W.locus) :
    (W.originalRestriction k hk).comp (W.containedRestriction j hW) =
      a.restriction k j (hk.trans hW) :=
  W.originalRestriction_comp_glue (W.containedChartPullbacks j hW)
    (W.containedChartPullbacks_compatible j hW) k hk

/-- The descended bounded map gives exactly the ambient inclusion on spectra. -/
theorem chart_containedRestriction (x : BanachSpectrum W.algebra) :
    a.chart j (BanachSpectrum.comap (W.containedRestriction j hW).toBoundedRingHom x) =
      W.chart x := by
  have hx : W.chart x ∈ W.locus := W.range_chart ▸ Set.mem_range_self x
  obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp (W.val.gluingData_locus.symm.subset hx)
  have hk := W.gluingIndex_subset i
  have hxy : BanachSpectrum.comap (W.originalRestriction _ hk).toBoundedRingHom y = x :=
    W.isEmbedding_chart.injective ((W.chart_originalRestriction _ hk y).trans hy)
  rw [← hxy]
  have hc := W.originalRestriction_comp_containedRestriction j hW _ hk
  have heq : BanachSpectrum.comap (W.containedRestriction j hW).toBoundedRingHom
      (BanachSpectrum.comap (W.originalRestriction _ hk).toBoundedRingHom y) =
        BanachSpectrum.comap (a.restriction _ j (hk.trans hW)).toBoundedRingHom y := by
    apply BanachSpectrum.ext
    intro b
    exact congrArg (fun q : BoundedAlgHom K (a.algebra j)
      (a.algebra (W.val.gluingData.index i)) => y (q b)) hc
  rw [heq, a.restriction_chart, W.chart_originalRestriction]

theorem injective_comap_containedRestriction :
    Function.Injective (BanachSpectrum.comap (W.containedRestriction j hW).toBoundedRingHom) := by
  intro x y hxy
  apply W.isEmbedding_chart.injective
  exact (W.chart_containedRestriction j hW x).symm.trans
    ((congrArg (a.chart j) hxy).trans (W.chart_containedRestriction j hW y))

theorem range_comap_containedRestriction :
    Set.range (BanachSpectrum.comap (W.containedRestriction j hW).toBoundedRingHom) =
      a.chart j ⁻¹' W.locus := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change a.chart j
      (BanachSpectrum.comap (W.containedRestriction j hW).toBoundedRingHom y) ∈ W.locus
    rw [W.chart_containedRestriction]
    exact W.range_chart ▸ Set.mem_range_self y
  · intro hx
    obtain ⟨y, hy⟩ := W.range_chart.symm ▸ hx
    exact ⟨y, (a.isEmbedding_chart j).injective
      ((W.chart_containedRestriction j hW y).trans hy)⟩

/-- A recognized subset contained in an original chart is a full represented
domain of that original algebra, retaining the entire descended bounded map. -/
theorem containedRestriction_represents :
    Represents K (W.containedRestriction j hW) (a.chart j ⁻¹' W.locus) := by
  rw [← W.range_comap_containedRestriction j hW]
  apply W.componentCover.represents_of_finiteCover (W.containedRestriction j hW)
    (W.injective_comap_containedRestriction j hW)
  intro i
  let i' : Fin W.property.cover.size := i
  change Represents K
    ((W.property.componentDomain i').baseMap.comp (W.containedRestriction j hW))
    (Set.range (BanachSpectrum.comap
      ((W.property.componentDomain i').baseMap.comp
        (W.containedRestriction j hW)).toBoundedRingHom))
  have heq :
      (W.property.componentDomain i').baseMap.comp (W.containedRestriction j hW) =
        a.restriction (W.property.cover.index i') j ((W.component_subset i').trans hW) :=
    (congrArg
      (fun q : BoundedAlgHom K W.algebra (a.algebra (W.property.cover.index i')) =>
        q.comp (W.containedRestriction j hW))
      (W.componentDomain_baseMap i')).trans
        (W.originalRestriction_comp_containedRestriction j hW
          (W.property.cover.index i') (W.component_subset i'))
  apply (congrArg
    (fun q : BoundedAlgHom K (a.algebra j) (a.algebra (W.property.cover.index i')) =>
      Represents K q (Set.range (BanachSpectrum.comap q.toBoundedRingHom))) heq).mpr
  rw [a.range_restriction]
  exact a.restriction_represents _ j ((W.component_subset i').trans hW)

/-- The actual recognized algebra as a full domain of any original chart
containing its literal locus. -/
def containedDomain : Domain K (a.algebra j) where
  algebra := W.algebra
  baseMap := W.containedRestriction j hW
  locus := a.chart j ⁻¹' W.locus
  represents := W.containedRestriction_represents j hW

end Langlands.Analytic.IndexedAffinoidAtlas.RecognizedSubset
