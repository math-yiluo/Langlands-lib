import Langlands.Geometry.Analytic.StrongQuasiIsoDomainImage
import Langlands.Geometry.Analytic.AffinoidRealizationSpecialCover
import Langlands.Geometry.Analytic.AtlasIntersectionFiniteRecognition
import Langlands.Geometry.Analytic.RecognizedAtlasExtension

/-! # Actual recognized images under coherent strong quasi-isomorphisms -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsQuasiIso

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K} {f : StrongHom A B}
  (hf : f.IsQuasiIso)

/-- The literal image of a source saturated representative is an actual
local full domain in the original target atlas. -/
def saturatedImageIndex (s : A.atlas.saturatedAtlas.Index) : B.atlas.saturatedAtlas.Index :=
  ⟨(hf.domainImage (A.atlas.saturatedRepresentative s)).locus, ⟨_, rfl⟩⟩

theorem saturatedImage_range (s : A.atlas.saturatedAtlas.Index) :
    Set.range (B.atlas.saturatedAtlas.chart (hf.saturatedImageIndex s)) =
      f.baseMap '' Set.range (A.atlas.saturatedAtlas.chart s) :=
  (B.atlas.range_saturatedChart _).trans
    ((hf.domainImage_locus (A.atlas.saturatedRepresentative s)).trans
      (congrArg (fun S => f.baseMap '' S)
        (A.atlas.saturatedRepresentative s).range_ambientMap.symm))

/-- The original source saturated algebra is unchanged in its image domain;
actual target local-domain uniqueness compares it with the chosen saturation. -/
def saturatedImageEquiv (s : A.atlas.saturatedAtlas.Index) :
    BoundedAlgEquiv K (A.atlas.saturatedAtlas.algebra s)
      (B.atlas.saturatedAtlas.algebra (hf.saturatedImageIndex s)) :=
  B.atlas.localDomainSaturatedEquiv
    (hf.domainImage (A.atlas.saturatedRepresentative s))

theorem saturatedImageEquiv_over_ambient
    (s : A.atlas.saturatedAtlas.Index)
    (x : BanachSpectrum (B.atlas.saturatedAtlas.algebra (hf.saturatedImageIndex s))) :
    f.baseMap (A.atlas.saturatedAtlas.chart s
        ((hf.saturatedImageEquiv s).spectrumHomeomorph x)) =
      B.atlas.saturatedAtlas.chart (hf.saturatedImageIndex s) x := by
  let U := hf.domainImage (A.atlas.saturatedRepresentative s)
  let S := hf.saturatedImageIndex s
  let q := LocalDomain.isoOfLocusEq U (B.atlas.saturatedRepresentative S)
    (B.atlas.saturatedRepresentative_locus S).symm
  exact (hf.domainImage_ambientMap (A.atlas.saturatedRepresentative s)
    ((hf.saturatedImageEquiv s).spectrumHomeomorph x)).symm.trans
      (q.inv.ambientMap_naturality x)

theorem saturatedImage_subset (s t : A.atlas.saturatedAtlas.Index)
    (hst : Set.range (A.atlas.saturatedAtlas.chart s) ⊆
      Set.range (A.atlas.saturatedAtlas.chart t)) :
    Set.range (B.atlas.saturatedAtlas.chart (hf.saturatedImageIndex s)) ⊆
      Set.range (B.atlas.saturatedAtlas.chart (hf.saturatedImageIndex t)) :=
  (hf.saturatedImage_range s).subset.trans
    ((Set.image_mono hst).trans (hf.saturatedImage_range t).symm.subset)

variable (hc : f.HasCoherentPullbacks)

include hc in
/-- Inverse local-domain comparison triangles and the unchanged image
functor restrictions prove full bounded naturality of the saturated maps. -/
theorem saturatedImageEquiv_naturality (s t : A.atlas.saturatedAtlas.Index)
    (hst : Set.range (A.atlas.saturatedAtlas.chart s) ⊆
      Set.range (A.atlas.saturatedAtlas.chart t)) :
    (B.atlas.saturatedAtlas.restriction (hf.saturatedImageIndex s)
      (hf.saturatedImageIndex t) (hf.saturatedImage_subset s t hst)).comp
        (hf.saturatedImageEquiv t).toBoundedAlgHom =
      (hf.saturatedImageEquiv s).toBoundedAlgHom.comp
        (A.atlas.saturatedAtlas.restriction s t hst) := by
  let S := hf.saturatedImageIndex s
  let T := hf.saturatedImageIndex t
  let U := hf.domainImage (A.atlas.saturatedRepresentative s)
  let V := hf.domainImage (A.atlas.saturatedRepresentative t)
  let q := LocalDomain.isoOfLocusEq U (B.atlas.saturatedRepresentative S)
    (B.atlas.saturatedRepresentative_locus S).symm
  let r := LocalDomain.isoOfLocusEq V (B.atlas.saturatedRepresentative T)
    (B.atlas.saturatedRepresentative_locus T).symm
  let p := (hf.domainImageFunctor hc).map (A.atlas.saturatedInclusion s t hst)
  let g := B.atlas.saturatedInclusion S T (hf.saturatedImage_subset s t hst)
  have h : g ≫ r.inv = q.inv ≫ p :=
    @Subsingleton.elim (LocalDomain.Inclusion (B.atlas.saturatedRepresentative S) V)
      inferInstance _ _
  exact congrArg LocalDomain.Inclusion.restriction h

variable (V : A.atlas.saturatedAtlas.RecognizedSubset)

/-- Every contained source saturated component retains a full representation
over V, with target saturated algebra and the transported ambient chart. -/
def recognitionImageChartDomain (s : A.atlas.saturatedAtlas.Index)
    (hs : Set.range (A.atlas.saturatedAtlas.chart s) ⊆ V.locus) :
    Domain K V.algebra where
  algebra := B.atlas.saturatedAtlas.algebra (hf.saturatedImageIndex s)
  baseMap := (hf.saturatedImageEquiv s).toBoundedAlgHom.comp (V.originalRestriction s hs)
  locus := (f.baseMap.comp V.chart) ⁻¹'
    Set.range (B.atlas.saturatedAtlas.chart (hf.saturatedImageIndex s))
  represents := by
    rw [hf.saturatedImage_range]
    change Represents K _ (V.chart ⁻¹'
      (f.baseMap ⁻¹' (f.baseMap '' Set.range (A.atlas.saturatedAtlas.chart s))))
    have hinj : Function.Injective f.baseMap := hf.1.homeomorph.injective
    rw [Set.preimage_image_eq _ hinj]
    exact (V.originalDomain s hs).represents.postcomp_equiv (hf.saturatedImageEquiv s)

theorem recognitionImageChartDomain_over_ambient (s : A.atlas.saturatedAtlas.Index)
    (hs : Set.range (A.atlas.saturatedAtlas.chart s) ⊆ V.locus)
    (x : BanachSpectrum (B.atlas.saturatedAtlas.algebra (hf.saturatedImageIndex s))) :
    f.baseMap (V.chart ((hf.recognitionImageChartDomain V s hs).spectrumMap x)) =
      B.atlas.saturatedAtlas.chart (hf.saturatedImageIndex s) x :=
  (congrArg f.baseMap (V.chart_originalRestriction s hs
    ((hf.saturatedImageEquiv s).spectrumHomeomorph x))).trans
      (hf.saturatedImageEquiv_over_ambient s x)

include hc in
theorem recognitionImageChartDomain_naturality (s t : A.atlas.saturatedAtlas.Index)
    (hs : Set.range (A.atlas.saturatedAtlas.chart s) ⊆ V.locus)
    (ht : Set.range (A.atlas.saturatedAtlas.chart t) ⊆ V.locus)
    (hst : Set.range (A.atlas.saturatedAtlas.chart s) ⊆
      Set.range (A.atlas.saturatedAtlas.chart t)) :
    (B.atlas.saturatedAtlas.restriction (hf.saturatedImageIndex s)
      (hf.saturatedImageIndex t) (hf.saturatedImage_subset s t hst)).comp
        (hf.recognitionImageChartDomain V t ht).baseMap =
      (hf.recognitionImageChartDomain V s hs).baseMap := by
  ext x
  exact (congrArg
    (fun q : BoundedAlgHom K (A.atlas.saturatedAtlas.algebra t)
      (B.atlas.saturatedAtlas.algebra (hf.saturatedImageIndex s)) =>
        q (V.originalRestriction t ht x))
    (hf.saturatedImageEquiv_naturality hc s t hst)).trans
      (congrArg (fun q : BoundedAlgHom K V.algebra (A.atlas.saturatedAtlas.algebra s) =>
        (hf.saturatedImageEquiv s) (q x))
        (V.originalRestriction_naturality t s ht hs hst))

/-- Transport the chosen recognized finite cover and every overlap to
the actual target saturated image indices. -/
def recognitionImageGluing : FiniteChartGluingData B.atlas.saturatedAtlas where
  size := V.property.cover.size
  index i := hf.saturatedImageIndex (V.property.cover.index i)
  overlap i j := hf.saturatedImageIndex (V.property.cover.overlap i j)
  overlap_range i j := by
    rw [hf.saturatedImage_range, V.property.cover.overlap_range,
      hf.saturatedImage_range, hf.saturatedImage_range]
    exact Set.image_inter hf.1.homeomorph.injective

theorem recognitionImageGluing_locus :
    (hf.recognitionImageGluing V).locus = f.baseMap '' V.locus := by
  change (⋃ i, Set.range (B.atlas.saturatedAtlas.chart
    (hf.saturatedImageIndex (V.property.cover.index i)))) = f.baseMap '' V.locus
  simp_rw [hf.saturatedImage_range]
  rw [← Set.image_iUnion]
  exact congrArg (fun S => f.baseMap '' S) V.property.cover_locus

/-- Full bounded compatibility supplies an actual finite realization on
the unchanged V algebra and the actual transported chart f composed with V. -/
def recognitionImageAffinoidRealization :
    (hf.recognitionImageGluing V).AffinoidRealization where
  algebra := V.algebra
  chart := f.baseMap.comp V.chart
  isEmbedding_chart := hf.1.homeomorph.isEmbedding.comp V.isEmbedding_chart
  range_chart := by
    change Set.range (f.baseMap ∘ V.chart) = _
    rw [Set.range_comp, V.range_chart, hf.recognitionImageGluing_locus]
  restriction i := (hf.recognitionImageChartDomain V
    (V.property.cover.index i) (V.component_subset i)).baseMap
  restriction_chart i x := hf.recognitionImageChartDomain_over_ambient V
    (V.property.cover.index i) (V.component_subset i) x
  represents i := (hf.recognitionImageChartDomain V
    (V.property.cover.index i) (V.component_subset i)).represents
  compatible i j := by
    let d := V.property.cover
    have hO : Set.range (A.atlas.saturatedAtlas.chart (d.overlap i j)) ⊆ V.locus :=
      (d.overlap_subset_left i j).trans (V.component_subset i)
    exact (hf.recognitionImageChartDomain_naturality hc V
      (d.overlap i j) (d.index i) hO (V.component_subset i)
        (d.overlap_subset_left i j)).trans
      (hf.recognitionImageChartDomain_naturality hc V
        (d.overlap i j) (d.index j) hO (V.component_subset j)
          (d.overlap_subset_right i j)).symm

include hc in
theorem recognitionImageGluing_isSpecialCover :
    (hf.recognitionImageGluing V).IsSpecialCover :=
  (hf.recognitionImageAffinoidRealization hc V).isSpecialCover

/-- Image recognition is derived from the actual finite realization,
with no target recognition or section-algebra comparison input. -/
def recognizedImage : B.atlas.saturatedAtlas.RecognizedSubset :=
  (hf.recognitionImageAffinoidRealization hc V).recognizedSubset

@[simp]
theorem recognizedImage_locus :
    (hf.recognizedImage hc V).locus = f.baseMap '' V.locus :=
  hf.recognitionImageGluing_locus V

def recognizedImageEquiv :
    BoundedAlgEquiv K V.algebra (hf.recognizedImage hc V).algebra :=
  (hf.recognitionImageAffinoidRealization hc V).recognitionEquiv

theorem recognizedImage_chart (x : BanachSpectrum (hf.recognizedImage hc V).algebra) :
    (hf.recognizedImage hc V).chart x =
      f.baseMap (V.chart ((hf.recognizedImageEquiv hc V).spectrumHomeomorph x)) :=
  (hf.recognitionImageAffinoidRealization hc V).recognizedSubset_chart x

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsQuasiIso
