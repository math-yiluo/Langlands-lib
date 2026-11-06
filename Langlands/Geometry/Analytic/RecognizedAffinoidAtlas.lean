import Langlands.Geometry.Analytic.RecognizedOriginalDomains
import Langlands.Geometry.Analytic.RecognizedAffinoidNet

/-! # The actual affinoid atlas on recognized literal subsets -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

namespace RecognizedSubset

variable {a} (U V : a.RecognizedSubset)

/-- The witnessed covering-domain condition supplies a genuine finite
full-domain cover of the constructed recognized presentation. -/
def componentCover : Domain.FiniteCover (Domain.whole K U.algebra) where
  size := U.property.cover.size
  obj := U.property.componentDomain
  map i := ⟨(U.property.componentDomain i).baseMap, rfl⟩
  covers x _ := by
    have hx : U.chart x ∈ U.locus := U.range_chart ▸ Set.mem_range_self x
    have hx' : U.chart x ∈ U.property.cover.locus := U.property.cover_locus.symm ▸ hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx'
    exact ⟨i, hi⟩

theorem component_subset (i : Fin U.property.cover.size) :
    Set.range (a.chart (U.property.cover.index i)) ⊆ U.locus := by
  intro x hx
  change x ∈ U.val.val
  exact U.property.cover_locus ▸ Set.mem_iUnion.mpr ⟨i, hx⟩

/-- The witnessed component map is the canonical restriction to that
original chart, as an equality of entire bounded maps. -/
theorem componentDomain_baseMap (i : Fin U.property.cover.size) :
    (U.property.componentDomain i).baseMap =
      U.originalRestriction (U.property.cover.index i) (U.component_subset i) :=
  congrArg
    (fun q : BoundedAlgHom K U.val.SectionAlgebra
      (a.algebra (U.property.cover.index i)) =>
      q.comp U.property.algebraEquiv.toBoundedAlgHom)
    (U.val.gluingData.projection_comp_restrictionTo U.property.cover
      (U.property.cover_locus.trans U.val.gluingData_locus.symm).subset i)

/-- Original restrictions commute with the constructed restriction
between nested recognized subsets, with their full original algebras. -/
theorem originalRestriction_comp_restriction (hUV : U.locus ⊆ V.locus)
    (parent : a.Index) (hp : Set.range (a.chart parent) ⊆ U.locus) :
    (U.originalRestriction parent hp).comp (U.restriction V hUV) =
      V.originalRestriction parent (hp.trans hUV) := by
  apply BoundedAlgHom.ext
  intro b
  change U.val.gluingData.originalRestriction parent
      (hp.trans U.val.gluingData_locus.symm.subset)
      (U.property.algebraEquiv
        (U.property.algebraEquiv.symm
          (U.val.restriction V.val hUV (V.property.algebraEquiv b)))) =
    V.val.gluingData.originalRestriction parent
      ((hp.trans hUV).trans V.val.gluingData_locus.symm.subset)
      (V.property.algebraEquiv b)
  rw [U.property.algebraEquiv.apply_symm_apply]
  exact congrArg
    (fun q : BoundedAlgHom K V.val.SectionAlgebra (a.algebra parent) =>
      q (V.property.algebraEquiv b))
    (V.val.gluingData.originalRestriction_comp_restrictionTo U.val.gluingData
      (U.val.gluingData_subset V.val hUV) parent
      (hp.trans U.val.gluingData_locus.symm.subset))

theorem injective_comap_restriction (hUV : U.locus ⊆ V.locus) :
    Function.Injective (BanachSpectrum.comap (U.restriction V hUV).toBoundedRingHom) := by
  intro x y hxy
  apply U.isEmbedding_chart.injective
  exact (U.chart_restriction V hUV x).symm.trans
    ((congrArg V.chart hxy).trans (U.chart_restriction V hUV y))

theorem range_comap_restriction (hUV : U.locus ⊆ V.locus) :
    Set.range (BanachSpectrum.comap (U.restriction V hUV).toBoundedRingHom) =
      V.chart ⁻¹' U.locus := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    change V.chart
      (BanachSpectrum.comap (U.restriction V hUV).toBoundedRingHom y) ∈ U.locus
    rw [U.chart_restriction V hUV y]
    exact U.range_chart ▸ Set.mem_range_self y
  · intro hx
    obtain ⟨y, hy⟩ := U.range_chart.symm ▸ hx
    exact ⟨y, V.isEmbedding_chart.injective
      ((U.chart_restriction V hUV y).trans hy)⟩

/-- Every recognized inclusion is a full affinoid-domain representation:
finite source recognition reduces it to the proved original-chart case. -/
theorem restriction_represents (hUV : U.locus ⊆ V.locus) :
    Represents K (U.restriction V hUV) (V.chart ⁻¹' U.locus) := by
  rw [← U.range_comap_restriction V hUV]
  apply U.componentCover.represents_of_finiteCover (U.restriction V hUV)
    (U.injective_comap_restriction V hUV)
  intro i
  let j : Fin U.property.cover.size := i
  change Represents K
    ((U.property.componentDomain j).baseMap.comp (U.restriction V hUV))
    (Set.range (BanachSpectrum.comap
      ((U.property.componentDomain j).baseMap.comp (U.restriction V hUV)).toBoundedRingHom))
  have heq :
      (U.property.componentDomain j).baseMap.comp (U.restriction V hUV) =
        V.originalRestriction (U.property.cover.index j)
          ((U.component_subset j).trans hUV) :=
    (congrArg
      (fun q : BoundedAlgHom K U.algebra (a.algebra (U.property.cover.index j)) =>
        q.comp (U.restriction V hUV))
      (U.componentDomain_baseMap j)).trans
        (U.originalRestriction_comp_restriction V hUV
          (U.property.cover.index j) (U.component_subset j))
  exact (congrArg
    (fun q : BoundedAlgHom K V.algebra (a.algebra (U.property.cover.index j)) =>
      Represents K q (Set.range (BanachSpectrum.comap q.toBoundedRingHom))) heq).mpr
        (V.originalRestriction_represents (U.property.cover.index j)
          ((U.component_subset j).trans hUV))

/-- The output domain retains the actual constructed source presentation,
the actual bounded restriction, and the literal relative subset. -/
def inclusionDomain (hUV : U.locus ⊆ V.locus) : Domain K V.algebra where
  algebra := U.algebra
  baseMap := U.restriction V hUV
  locus := V.chart ⁻¹' U.locus
  represents := U.restriction_represents V hUV

end RecognizedSubset

/-- The actual atlas on intrinsically recognized special subsets. The
new algebras, charts, full restrictions and net are all constructed. -/
def recognitionAtlas : IndexedAffinoidAtlas.{u, v, v} K X where
  Index := a.RecognizedSubset
  algebra U := U.algebra
  chart U := U.chart
  isEmbedding_chart U := U.isEmbedding_chart
  chartDomain_injective U V h := by
    apply Subtype.ext
    apply Subtype.ext
    exact U.range_chart.symm.trans (h.trans V.range_chart)
  locallyHausdorff := a.locallyHausdorff
  isNet_chartFamily := RecognizedSubset.isNet_chartFamily a
  restriction U V h := U.restriction V (by
    rw [← U.range_chart, ← V.range_chart]
    exact h)
  restriction_chart U V h x := U.chart_restriction V _ x
  restriction_universal U V h R φ hφ := by
    apply (U.restriction_represents V
      (U.range_chart.symm.subset.trans (h.trans V.range_chart.subset))).2.2 R φ
    intro x
    exact U.range_chart ▸ hφ x
  restriction_id U _ := U.restriction_self
  restriction_comp U V W _ _ _ := (U.restriction_comp V W _ _).symm

def originalRecognitionIndex (parent : a.Index) : a.recognitionAtlas.Index :=
  ⟨SpecialSubset.original a parent, SpecialSubset.original_isRecognized a parent⟩

theorem recognitionAtlas_original_range (parent : a.Index) :
    Set.range (a.recognitionAtlas.chart (a.originalRecognitionIndex parent)) =
      Set.range (a.chart parent) :=
  (a.originalRecognitionIndex parent).range_chart

/-- The extension compares with every unchanged original algebra by a
constructed bounded equivalence, not a supplied presentation comparison. -/
def originalRecognitionAlgebraEquiv (parent : a.Index) :
    BoundedAlgEquiv K (a.algebra parent)
      (a.recognitionAtlas.algebra (a.originalRecognitionIndex parent)) :=
  (SpecialSubset.originalAlgebraEquiv a parent).trans
    (a.originalRecognitionIndex parent).property.algebraEquiv.symm

theorem recognitionAtlas_original_chart (parent : a.Index)
    (x : BanachSpectrum (a.recognitionAtlas.algebra (a.originalRecognitionIndex parent))) :
    a.recognitionAtlas.chart (a.originalRecognitionIndex parent) x =
      a.chart parent ((a.originalRecognitionAlgebraEquiv parent).spectrumHomeomorph x) :=
  SpecialSubset.original_chart a parent _ _ x

/-- The actual source full-net recognition atlas uses special covers from
the already constructed enlarged full local-domain net. -/
def fullRecognitionAtlas : IndexedAffinoidAtlas.{u, v, v} K X :=
  a.saturatedAtlas.recognitionAtlas

theorem fullRecognitionAtlas_chartFamily :
    Set.range (fun i => Set.range (a.fullRecognitionAtlas.chart i)) =
      a.recognizedAffinoidFamily :=
  RecognizedSubset.chartFamily_eq_family a.saturatedAtlas

theorem fullRecognitionAtlas_localDomain_range (U : LocalDomain a) :
    Set.range (a.fullRecognitionAtlas.chart (a.recognizedLocalDomain U)) = U.locus :=
  (a.recognizedLocalDomain U).range_chart.trans (a.recognizedLocalDomain_locus U)

end Langlands.Analytic.IndexedAffinoidAtlas
