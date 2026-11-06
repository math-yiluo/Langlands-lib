import Langlands.Geometry.Analytic.IteratedRecognizedDomainRefinement
import Langlands.Geometry.Analytic.NestedRecognitionOriginalDomains
import Langlands.Geometry.Analytic.RecognizedDomainClosure

/-! # Constructed recognition idempotence on literal affinoid chart families -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  (W : a.fullRecognitionAtlas.saturatedAtlas.RecognizedSubset)

theorem iteratedRecognitionChartIndex_subset
    (i : Fin (a.iteratedRecognitionDomainCover W).size) :
    Set.range (a.saturatedAtlas.chart (a.iteratedRecognitionChartIndex W i)) ⊆ W.locus := by
  intro x hx
  exact a.iteratedRecognitionChartIndex_covers W ▸ Set.mem_iUnion.mpr ⟨i, hx⟩

/-- The flattened chart loci carry canonical full maps through the actual
nested atlases, with full original-chart restriction naturality. -/
def iteratedRecognitionCanonicalComponent
    (i : Fin (a.iteratedRecognitionDomainCover W).size) : Domain K W.algebra :=
  a.saturatedAtlas.recognitionChartDomain W (a.iteratedRecognitionChartIndex W i)
    (a.iteratedRecognitionChartIndex_subset W i)

theorem iteratedRecognitionCanonicalComponent_locus
    (i : Fin (a.iteratedRecognitionDomainCover W).size) :
    (a.iteratedRecognitionCanonicalComponent W i).locus =
      W.chart ⁻¹' Set.range (a.saturatedAtlas.chart (a.iteratedRecognitionChartIndex W i)) :=
  a.saturatedAtlas.recognitionChartDomain_locus W _ _

theorem iteratedRecognitionCanonicalComponent_over_ambient
    (i : Fin (a.iteratedRecognitionDomainCover W).size)
    (x : BanachSpectrum (a.saturatedAtlas.algebra (a.iteratedRecognitionChartIndex W i))) :
    W.chart ((a.iteratedRecognitionCanonicalComponent W i).spectrumMap x) =
      a.saturatedAtlas.chart (a.iteratedRecognitionChartIndex W i) x :=
  a.saturatedAtlas.recognitionChartDomain_over_ambient W _ _ x

/-- Actual pushout overlap quotients over the unchanged iterated parent,
extended through their original first-saturation local representatives. -/
def iteratedRecognitionOverlap (i j : Fin (a.iteratedRecognitionDomainCover W).size) :
    LocalDomain a :=
  (a.saturatedRepresentative (a.iteratedRecognitionChartIndex W i)).extend
    ((a.iteratedRecognitionCanonicalComponent W i).relative
      ((a.iteratedRecognitionCanonicalComponent W i).inter
        (a.iteratedRecognitionCanonicalComponent W j))
      ((a.iteratedRecognitionCanonicalComponent W i).interLeft
        (a.iteratedRecognitionCanonicalComponent W j)))

theorem iteratedRecognitionOverlap_locus
    (i j : Fin (a.iteratedRecognitionDomainCover W).size) :
    (a.iteratedRecognitionOverlap W i j).locus =
      Set.range (a.saturatedAtlas.chart (a.iteratedRecognitionChartIndex W i)) ∩
        Set.range (a.saturatedAtlas.chart (a.iteratedRecognitionChartIndex W j)) := by
  let E := a.iteratedRecognitionCanonicalComponent W i
  let F := a.iteratedRecognitionCanonicalComponent W j
  let U := a.saturatedRepresentative (a.iteratedRecognitionChartIndex W i)
  have hmap : U.ambientMap = W.chart.comp E.spectrumMap :=
    ContinuousMap.ext fun x => (a.iteratedRecognitionCanonicalComponent_over_ambient W i x).symm
  have himage : (a.iteratedRecognitionOverlap W i j).locus =
      W.chart '' (E.inter F).locus := by
    calc
      _ = U.ambientMap '' (E.relative (E.inter F) (E.interLeft F)).locus :=
        LocalDomain.extend_locus _ _
      _ = (W.chart.comp E.spectrumMap) '' (E.relative (E.inter F) (E.interLeft F)).locus :=
        congrArg (fun f : C(BanachSpectrum E.algebra, X) =>
          f '' (E.relative (E.inter F) (E.interLeft F)).locus) hmap
      _ = W.chart '' (E.spectrumMap '' (E.relative (E.inter F) (E.interLeft F)).locus) :=
        (Set.image_image W.chart E.spectrumMap
          (E.relative (E.inter F) (E.interLeft F)).locus).symm
      _ = W.chart '' (E.inter F).locus :=
        congrArg (fun S => W.chart '' S) (E.image_relative_locus _ _)
  apply himage.trans
  change W.chart '' (E.locus ∩ F.locus) = _
  dsimp only [E, F]
  rw [a.iteratedRecognitionCanonicalComponent_locus, a.iteratedRecognitionCanonicalComponent_locus]
  ext x
  constructor
  · rintro ⟨y, ⟨hyE, hyF⟩, rfl⟩
    exact ⟨hyE, hyF⟩
  · intro hx
    have hxW : x ∈ Set.range W.chart :=
      W.range_chart.symm ▸ a.iteratedRecognitionChartIndex_subset W i hx.1
    obtain ⟨y, rfl⟩ := hxW
    exact ⟨y, hx, rfl⟩

/-- Actual original first-saturation charts and represented quotient
overlaps for the iterated recognized locus. -/
def iteratedRecognitionGluing : FiniteChartGluingData a.saturatedAtlas where
  size := (a.iteratedRecognitionDomainCover W).size
  index := a.iteratedRecognitionChartIndex W
  overlap i j := ⟨(a.iteratedRecognitionOverlap W i j).locus, ⟨_, rfl⟩⟩
  overlap_range i j :=
    (a.range_saturatedChart _).trans (a.iteratedRecognitionOverlap_locus W i j)

theorem iteratedRecognitionGluing_locus :
    (a.iteratedRecognitionGluing W).locus = W.locus :=
  a.iteratedRecognitionChartIndex_covers W

/-- Every realization field is constructed, including compatibility of
the entire bounded maps through the canonical nested restrictions. -/
def iteratedRecognitionAffinoidRealization :
    (a.iteratedRecognitionGluing W).AffinoidRealization where
  algebra := W.algebra
  chart := W.chart
  isEmbedding_chart := W.isEmbedding_chart
  range_chart := W.range_chart.trans (a.iteratedRecognitionGluing_locus W).symm
  restriction i := (a.iteratedRecognitionCanonicalComponent W i).baseMap
  restriction_chart i x := a.iteratedRecognitionCanonicalComponent_over_ambient W i x
  represents i := (a.iteratedRecognitionCanonicalComponent_locus W i) ▸
    (a.iteratedRecognitionCanonicalComponent W i).represents
  compatible i j := by
    let d := a.iteratedRecognitionGluing W
    have hO : Set.range (a.saturatedAtlas.chart (d.overlap i j)) ⊆ W.locus :=
      (d.overlap_subset_left i j).trans (a.iteratedRecognitionChartIndex_subset W i)
    exact (a.saturatedAtlas.recognitionChartDomain_naturality W
      (d.overlap i j) (d.index i) hO (a.iteratedRecognitionChartIndex_subset W i)
        (d.overlap_subset_left i j)).trans
      (a.saturatedAtlas.recognitionChartDomain_naturality W
        (d.overlap i j) (d.index j) hO (a.iteratedRecognitionChartIndex_subset W j)
          (d.overlap_subset_right i j)).symm

def iteratedRecognitionOverlapEquiv
    (i j : Fin (a.iteratedRecognitionDomainCover W).size) :
    BoundedAlgEquiv K
      ((a.iteratedRecognitionCanonicalComponent W i).inter
        (a.iteratedRecognitionCanonicalComponent W j)).algebra
      (a.saturatedAtlas.algebra ((a.iteratedRecognitionGluing W).overlap i j)) :=
  a.localDomainSaturatedEquiv (a.iteratedRecognitionOverlap W i j)

theorem iteratedRecognitionGluing_leftRestriction
    (i j : Fin (a.iteratedRecognitionDomainCover W).size) :
    (a.iteratedRecognitionGluing W).leftRestriction i j =
      (a.iteratedRecognitionOverlapEquiv W i j).toBoundedAlgHom.comp
        (AffinoidPushout.leftMap
          (a.iteratedRecognitionCanonicalComponent W i).baseMap
          (a.iteratedRecognitionCanonicalComponent W j).baseMap) := by
  let d := a.iteratedRecognitionGluing W
  let E := a.iteratedRecognitionCanonicalComponent W i
  let F := a.iteratedRecognitionCanonicalComponent W j
  let U := a.saturatedRepresentative (a.iteratedRecognitionChartIndex W i)
  let R : Domain K U.algebra := E.relative (E.inter F) (E.interLeft F)
  let L := a.iteratedRecognitionOverlap W i j
  let e := LocalDomain.isoOfLocusEq L (a.saturatedRepresentative (d.overlap i j))
    (a.saturatedRepresentative_locus (d.overlap i j)).symm
  have h : e.inv ≫ U.extendInclusion R =
      a.saturatedInclusion (d.overlap i j) (d.index i) (d.overlap_subset_left i j) :=
    @Subsingleton.elim
      (LocalDomain.Inclusion (a.saturatedRepresentative (d.overlap i j)) U) inferInstance _ _
  exact (congrArg LocalDomain.Inclusion.restriction h).symm

theorem iteratedRecognitionGluing_rightRestriction
    (i j : Fin (a.iteratedRecognitionDomainCover W).size) :
    (a.iteratedRecognitionGluing W).rightRestriction i j =
      (a.iteratedRecognitionOverlapEquiv W i j).toBoundedAlgHom.comp
        (AffinoidPushout.rightMap
          (a.iteratedRecognitionCanonicalComponent W i).baseMap
          (a.iteratedRecognitionCanonicalComponent W j).baseMap) := by
  let d := a.iteratedRecognitionGluing W
  let E := a.iteratedRecognitionCanonicalComponent W i
  let F := a.iteratedRecognitionCanonicalComponent W j
  let e := a.iteratedRecognitionOverlapEquiv W i j
  apply F.represents.hom_ext (a.saturatedAtlas.algebra (d.overlap i j))
  ext x
  have hc := congrArg
    (fun q : BoundedAlgHom K W.algebra (a.saturatedAtlas.algebra (d.overlap i j)) => q x)
    ((a.iteratedRecognitionAffinoidRealization W).compatible i j)
  have hl := congrArg
    (fun q : BoundedAlgHom K E.algebra (a.saturatedAtlas.algebra (d.overlap i j)) =>
      q (E.baseMap x)) (a.iteratedRecognitionGluing_leftRestriction W i j)
  have hp := congrArg
    (fun q : BoundedAlgHom K W.algebra (E.inter F).algebra => e (q x))
    (AffinoidPushout.condition E.baseMap F.baseMap)
  exact hc.symm.trans (hl.trans hp)

theorem iteratedRecognitionGluing_overlapTensorMap
    (i j : Fin (a.iteratedRecognitionDomainCover W).size) :
    (a.iteratedRecognitionGluing W).overlapTensorMap i j =
      (a.iteratedRecognitionOverlapEquiv W i j).toBoundedAlgHom.comp
        (AffinoidPushout.tensorMap
          (a.iteratedRecognitionCanonicalComponent W i).baseMap
          (a.iteratedRecognitionCanonicalComponent W j).baseMap) := by
  let d := a.iteratedRecognitionGluing W
  let E := a.iteratedRecognitionCanonicalComponent W i
  let F := a.iteratedRecognitionCanonicalComponent W j
  let e := a.iteratedRecognitionOverlapEquiv W i j
  apply CompletedTensorAlgebra.hom_ext
  · ext x
    have ht := congrArg
      (fun q : BoundedAlgHom K E.algebra (a.saturatedAtlas.algebra (d.overlap i j)) => q x)
      (d.overlapTensorMap_comp_leftMap i j)
    have hl := congrArg
      (fun q : BoundedAlgHom K E.algebra (a.saturatedAtlas.algebra (d.overlap i j)) => q x)
      (a.iteratedRecognitionGluing_leftRestriction W i j)
    have hp := congrArg
      (fun q : BoundedAlgHom K E.algebra (E.inter F).algebra => e (q x))
      (AffinoidPushout.tensorMap_comp_leftMap E.baseMap F.baseMap)
    exact ht.trans (hl.trans hp.symm)
  · ext x
    have ht := congrArg
      (fun q : BoundedAlgHom K F.algebra (a.saturatedAtlas.algebra (d.overlap i j)) => q x)
      (d.overlapTensorMap_comp_rightMap i j)
    have hr := congrArg
      (fun q : BoundedAlgHom K F.algebra (a.saturatedAtlas.algebra (d.overlap i j)) => q x)
      (a.iteratedRecognitionGluing_rightRestriction W i j)
    have hp := congrArg
      (fun q : BoundedAlgHom K F.algebra (E.inter F).algebra => e (q x))
      (AffinoidPushout.tensorMap_comp_rightMap E.baseMap F.baseMap)
    exact ht.trans (hr.trans hp.symm)

theorem iteratedRecognitionGluing_tensor_isAdmissibleEpi
    (i j : Fin (a.iteratedRecognitionDomainCover W).size) :
    ((a.iteratedRecognitionGluing W).overlapTensorMap i j).IsAdmissibleEpi := by
  let e := a.iteratedRecognitionOverlapEquiv W i j
  have he : e.toBoundedAlgHom.IsAdmissibleEpi := by
    apply e.toBoundedAlgHom.isAdmissibleEpi_of_bounded_section e.symm.toBoundedAlgHom
    ext x
    exact e.apply_symm_apply x
  rw [a.iteratedRecognitionGluing_overlapTensorMap]
  exact BoundedAlgHom.IsAdmissibleEpi.comp _ _
    (AffinoidPushout.tensorMap_isAdmissibleEpi _ _) he

theorem iteratedRecognitionGluing_isSpecialCover :
    (a.iteratedRecognitionGluing W).IsSpecialCover :=
  ⟨(a.iteratedRecognitionAffinoidRealization W).locusHomeomorph.symm.t2Space,
    a.iteratedRecognitionGluing_tensor_isAdmissibleEpi W⟩

/-- The literal iterated recognized locus has an actual special cover in
the original first-saturation atlas. -/
def iteratedRecognitionSpecialSubset : a.saturatedAtlas.SpecialSubset :=
  ⟨W.locus, a.iteratedRecognitionGluing W, a.iteratedRecognitionGluing_locus W,
    a.iteratedRecognitionGluing_isSpecialCover W⟩

/-- Construct an old recognized index for every iterated full-recognition
chart, supplying all three intrinsic recognition conditions. -/
def fullRecognitionIdempotenceIndex : a.fullRecognitionAtlas.Index :=
  ⟨a.iteratedRecognitionSpecialSubset W,
    (a.iteratedRecognitionSpecialSubset W).isRecognized_of_affinoidRealization
      (a.iteratedRecognitionGluing W) (a.iteratedRecognitionGluing_locus W)
      (a.iteratedRecognitionGluing_isSpecialCover W)
      (a.iteratedRecognitionAffinoidRealization W)⟩

@[simp]
theorem fullRecognitionIdempotenceIndex_locus :
    (a.fullRecognitionIdempotenceIndex W).locus = W.locus := rfl

/-- The original iterated algebra and its reconstructed old presentation
are compared by actual bounded mutually inverse algebra maps. -/
def fullRecognitionIdempotenceAlgebraEquiv :
    BoundedAlgEquiv K W.algebra (a.fullRecognitionIdempotenceIndex W).algebra :=
  ((a.iteratedRecognitionSpecialSubset W).realizationSectionEquiv
    (a.iteratedRecognitionGluing W) (a.iteratedRecognitionGluing_locus W)
    (a.iteratedRecognitionAffinoidRealization W)).trans
      (a.fullRecognitionIdempotenceIndex W).property.algebraEquiv.symm

theorem fullRecognitionIdempotenceIndex_chart
    (x : BanachSpectrum (a.fullRecognitionIdempotenceIndex W).algebra) :
    (a.fullRecognitionIdempotenceIndex W).chart x =
      W.chart ((a.fullRecognitionIdempotenceAlgebraEquiv W).spectrumHomeomorph x) :=
  (a.iteratedRecognitionSpecialSubset W).chart_affinoidRealization
    (a.fullRecognitionIdempotenceIndex W).property.affinoid
    (a.fullRecognitionIdempotenceIndex W).property.bijective
    (a.iteratedRecognitionGluing W) (a.iteratedRecognitionGluing_locus W)
    (a.iteratedRecognitionAffinoidRealization W) x

include a in
/-- Iterating full recognition adds no literal affinoid chart range. -/
theorem fullRecognitionAtlas_chartFamily_idempotent :
    Set.range (fun i => Set.range (a.fullRecognitionAtlas.fullRecognitionAtlas.chart i)) =
      Set.range (fun i => Set.range (a.fullRecognitionAtlas.chart i)) := by
  apply Set.Subset.antisymm
  · rintro S ⟨V, rfl⟩
    exact ⟨a.fullRecognitionIdempotenceIndex V,
      (a.fullRecognitionIdempotenceIndex V).range_chart.trans V.range_chart.symm⟩
  · rintro S ⟨V, rfl⟩
    let B := a.fullRecognitionAtlas
    exact ⟨B.recognizedLocalDomain (B.originalLocalDomain V),
      (B.fullRecognitionAtlas_localDomain_range (B.originalLocalDomain V)).trans
        (B.originalLocalDomain_locus V)⟩

end Langlands.Analytic.IndexedAffinoidAtlas
