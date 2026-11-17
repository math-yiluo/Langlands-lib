import Langlands.Geometry.Analytic.QuasiIsoFiniteEtale

/-! # Full recognition images of analytic domain embeddings -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Topology Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- An embedding whose complete bounded chart maps represent their actual images. -/
def IsDomainEmbedding (f : StrongHom A B) : Prop :=
  IsEmbedding f.baseMap ∧
    ∀ i j (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)),
      Represents K (f.pullback i j h) (f.chartImageLocus i j)

namespace IsDomainEmbedding

variable {f : StrongHom A B} (hf : f.IsDomainEmbedding)

/-- The represented image of a source chart retains its actual bounded pullback. -/
def localDomain (i : A.atlas.Index) (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    Domain K (B.atlas.algebra j) where
  algebra := A.atlas.algebra i
  baseMap := f.pullback i j h
  locus := f.chartImageLocus i j
  represents := hf.2 i j h

/-- Extend through the actual full representation of the source parent.
The represented algebra is the unchanged local source-domain algebra. -/
def domainImage (U : LocalDomain A.atlas) : LocalDomain B.atlas :=
  ⟨f.chosenTargetIndex U.index,
    (hf.localDomain U.index (f.chosenTargetIndex U.index)
      (f.chosenTarget_admissible U.index)).extend U.domain⟩

@[simp]
theorem domainImage_algebra (U : LocalDomain A.atlas) :
    (hf.domainImage U).algebra = U.algebra := rfl

@[simp]
theorem domainImage_baseMap (U : LocalDomain A.atlas) :
    (hf.domainImage U).domain.baseMap =
      U.domain.baseMap.comp
        (f.pullback U.index (f.chosenTargetIndex U.index)
          (f.chosenTarget_admissible U.index)) := rfl

/-- The actual spectrum realization is the original ambient map after `f`. -/
theorem domainImage_ambientMap (U : LocalDomain A.atlas) (x : BanachSpectrum U.algebra) :
    (hf.domainImage U).ambientMap x = f.baseMap (U.ambientMap x) := by
  exact f.chart_comm U.index (f.chosenTargetIndex U.index)
    (f.chosenTarget_admissible U.index) (U.domain.spectrumMap x)

/-- This is equality of actual ambient subsets, with no chart replacement. -/
theorem domainImage_locus (U : LocalDomain A.atlas) :
    (hf.domainImage U).locus = f.baseMap '' U.locus := by
  rw [← LocalDomain.range_ambientMap, ← U.range_ambientMap, ← Set.range_comp]
  exact congrArg Set.range (funext (hf.domainImage_ambientMap U))

/-- Reexpression over every containing target chart recovers the complete
constructed local pullback, on the unchanged source-domain algebra. -/
theorem domainImage_chartRestriction (U : LocalDomain A.atlas) (j : B.atlas.Index)
    (h : (hf.domainImage U).locus ⊆ Set.range (B.atlas.chart j))
    (hU : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j)) :
    B.atlas.domainChartRestriction (hf.domainImage U).index j
        (hf.domainImage U).domain h = f.localChartPullback U j hU := by
  exact B.atlas.domainChartRestriction_eq_changeMapChart
    (hf.domainImage U).index j (hf.domainImage U).domain h

/-- Original full coefficient coherence proves that every source bounded
restriction is also an actual restriction between the image domains. -/
def domainImageMap (hc : f.HasCoherentPullbacks) {U V : LocalDomain A.atlas}
    (p : U ⟶ V) : hf.domainImage U ⟶ hf.domainImage V where
  subset := by
    rw [hf.domainImage_locus, hf.domainImage_locus]
    exact Set.image_mono p.subset
  restriction := p.restriction
  comp_chart j hU hV := by
    have hu : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j) := by
      rw [← hf.domainImage_locus U]
      exact hU
    have hv : f.baseMap '' V.locus ⊆ Set.range (B.atlas.chart j) := by
      rw [← hf.domainImage_locus V]
      exact hV
    rw [hf.domainImage_chartRestriction V j hV hv,
      hf.domainImage_chartRestriction U j hU hu]
    exact f.localChartPullback_source hc p j hu hv

@[simp]
theorem domainImageMap_restriction (hc : f.HasCoherentPullbacks)
    {U V : LocalDomain A.atlas} (p : U ⟶ V) :
    (hf.domainImageMap hc p).restriction = p.restriction := rfl

/-- Direct image retains every original quotient algebra and bounded arrow.
No closure, directedness or refinement assumption is required. -/
def domainImageFunctor (hc : f.HasCoherentPullbacks) :
    LocalDomain A.atlas ⥤ LocalDomain B.atlas where
  obj := hf.domainImage
  map := hf.domainImageMap hc
  map_id _ := LocalDomain.Inclusion.ext rfl
  map_comp _ _ := LocalDomain.Inclusion.ext rfl


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
    have hinj : Function.Injective f.baseMap := hf.1.injective
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
    exact Set.image_inter hf.1.injective

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
  isEmbedding_chart := hf.1.comp V.isEmbedding_chart
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


/-- The transported full-domain maps commute with every actual recognized
restriction in the source, on entire bounded algebras. -/
theorem recognitionImageChartDomain_comp_restriction
    (U V : A.atlas.saturatedAtlas.RecognizedSubset) (hUV : U.locus ⊆ V.locus)
    (s : A.atlas.saturatedAtlas.Index)
    (hs : Set.range (A.atlas.saturatedAtlas.chart s) ⊆ U.locus) :
    (hf.recognitionImageChartDomain U s hs).baseMap.comp (U.restriction V hUV) =
      (hf.recognitionImageChartDomain V s (hs.trans hUV)).baseMap := by
  exact congrArg
    (fun q : BoundedAlgHom K V.algebra (A.atlas.saturatedAtlas.algebra s) =>
      (hf.saturatedImageEquiv s).toBoundedAlgHom.comp q)
    (U.originalRestriction_comp_restriction V hUV s hs)

/-- The image of every source chart contained in a recognized subset is
contained in the actual recognized image. -/
theorem saturatedImage_subset_recognizedImage
    (V : A.atlas.saturatedAtlas.RecognizedSubset) (s : A.atlas.saturatedAtlas.Index)
    (hs : Set.range (A.atlas.saturatedAtlas.chart s) ⊆ V.locus) :
    Set.range (B.atlas.saturatedAtlas.chart (hf.saturatedImageIndex s)) ⊆
      (hf.recognizedImage hc V).locus :=
  (hf.saturatedImage_range s).subset.trans
    ((Set.image_mono hs).trans (hf.recognizedImage_locus hc V).symm.subset)

/-- The section restriction to every contained image chart recovers the
transported source map. Separation uses a constructed finite source cover. -/
theorem recognitionImage_originalRestriction
    (V : A.atlas.saturatedAtlas.RecognizedSubset) (s : A.atlas.saturatedAtlas.Index)
    (hs : Set.range (A.atlas.saturatedAtlas.chart s) ⊆ V.locus) :
    let d := hf.recognitionImageGluing V
    let c := hf.recognitionImageAffinoidRealization hc V
    letI : T2Space d.locus := c.locusHomeomorph.symm.t2Space
    (d.originalRestriction (hf.saturatedImageIndex s)
      (hf.saturatedImage_subset_recognizedImage hc V s hs)).comp c.restrictFromParent =
        (hf.recognitionImageChartDomain V s hs).baseMap := by
  let d := hf.recognitionImageGluing V
  let c := hf.recognitionImageAffinoidRealization hc V
  let : T2Space d.locus := c.locusHomeomorph.symm.t2Space
  let d0 := V.property.cover
  let C := d0.subordinateCoverOfHausdorff s (hs.trans V.property.cover_locus.symm.subset)
  let hs' := hf.saturatedImage_subset_recognizedImage hc V s hs
  have hn (k l : A.atlas.saturatedAtlas.Index)
      (hkl : Set.range (A.atlas.saturatedAtlas.chart k) ⊆
        Set.range (A.atlas.saturatedAtlas.chart l))
      (y : B.atlas.saturatedAtlas.algebra (hf.saturatedImageIndex l)) :
      (hf.saturatedImageEquiv k)
          (A.atlas.saturatedAtlas.restriction k l hkl ((hf.saturatedImageEquiv l).symm y)) =
        B.atlas.saturatedAtlas.restriction (hf.saturatedImageIndex k)
          (hf.saturatedImageIndex l) (hf.saturatedImage_subset k l hkl) y := by
    have h := congrArg
      (fun q : BoundedAlgHom K (A.atlas.saturatedAtlas.algebra l)
        (B.atlas.saturatedAtlas.algebra (hf.saturatedImageIndex k)) =>
          q ((hf.saturatedImageEquiv l).symm y))
      (hf.saturatedImageEquiv_naturality hc k l hkl)
    exact h.symm.trans (congrArg
      (B.atlas.saturatedAtlas.restriction (hf.saturatedImageIndex k)
        (hf.saturatedImageIndex l) (hf.saturatedImage_subset k l hkl))
      ((hf.saturatedImageEquiv l).apply_symm_apply y))
  ext x
  apply (hf.saturatedImageEquiv s).symm.injective
  apply C.domainCover.algebra_ext_of_restrict_eq
  intro t
  apply (hf.saturatedImageEquiv (C.index t)).injective
  have hd := d.original_comp_originalRestriction (hf.saturatedImageIndex s) hs'
    (hf.saturatedImageIndex (C.index t))
    (hf.saturatedImage_subset (C.index t) s (C.subset_parent t))
    (C.member t)
    (hf.saturatedImage_subset (C.index t) (d0.index (C.member t)) (C.subset_member t))
  have hm := hf.recognitionImageChartDomain_naturality hc V (C.index t)
    (d0.index (C.member t)) ((C.subset_parent t).trans hs)
    (V.component_subset (C.member t)) (C.subset_member t)
  have hp := hf.recognitionImageChartDomain_naturality hc V (C.index t) s
    ((C.subset_parent t).trans hs) hs (C.subset_parent t)
  exact (hn (C.index t) s (C.subset_parent t) _).trans
    ((congrArg
      (fun q : BoundedAlgHom K d.SectionAlgebra
        (B.atlas.saturatedAtlas.algebra (hf.saturatedImageIndex (C.index t))) =>
          q (c.restrictFromParent x)) hd).trans
      ((congrArg
        (fun q : BoundedAlgHom K V.algebra
          (B.atlas.saturatedAtlas.algebra (hf.saturatedImageIndex (C.index t))) => q x)
        hm).trans
          ((congrArg
            (fun q : BoundedAlgHom K V.algebra
              (B.atlas.saturatedAtlas.algebra (hf.saturatedImageIndex (C.index t))) => q x)
            hp).symm.trans
              (hn (C.index t) s (C.subset_parent t) _).symm)))

/-- The constructed bounded comparison recovers every original source
restriction after passage to its actual target image chart. -/
theorem recognizedImageEquiv_originalRestriction
    (V : A.atlas.saturatedAtlas.RecognizedSubset) (s : A.atlas.saturatedAtlas.Index)
    (hs : Set.range (A.atlas.saturatedAtlas.chart s) ⊆ V.locus) :
    ((hf.recognizedImage hc V).originalRestriction (hf.saturatedImageIndex s)
      (hf.saturatedImage_subset_recognizedImage hc V s hs)).comp
        (hf.recognizedImageEquiv hc V).toBoundedAlgHom =
      (hf.recognitionImageChartDomain V s hs).baseMap := by
  let d := hf.recognitionImageGluing V
  let c := hf.recognitionImageAffinoidRealization hc V
  let : T2Space d.locus := c.locusHomeomorph.symm.t2Space
  exact ((hf.recognizedImage hc V).originalRestriction_comp_affinoidRealization
    d rfl c (hf.saturatedImageIndex s)
    (hf.saturatedImage_subset_recognizedImage hc V s hs)).trans
      (hf.recognitionImage_originalRestriction hc V s hs)


/-- The actual enlarged pullback on a chart and its entire image is the
inverse of the constructed bounded image comparison. -/
theorem saturationExtension_pullback_saturatedImage
    (s : A.atlas.saturatedAtlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.saturatedAtlas.chart s) ⊆
      Set.range (B.atlas.saturatedAtlas.chart (hf.saturatedImageIndex s))) :
    (f.saturationExtension hc).pullback s (hf.saturatedImageIndex s) h =
      (hf.saturatedImageEquiv s).symm.toBoundedAlgHom := by
  let U := A.atlas.saturatedRepresentative s
  let D := hf.domainImage U
  let V := B.atlas.saturatedRepresentative (hf.saturatedImageIndex s)
  let e := LocalDomain.isoOfLocusEq D V
    (B.atlas.saturatedRepresentative_locus (hf.saturatedImageIndex s)).symm
  have hUV : f.baseMap '' U.locus ⊆ V.locus := by
    rw [← U.range_ambientMap, ← V.range_ambientMap]
    exact h
  change f.localDomainPullback U V hUV = e.hom.restriction
  symm
  apply f.localDomainPullback_unique
  have hD : D.locus ⊆ Set.range (B.atlas.chart V.index) :=
    e.hom.subset.trans
      (B.atlas.domainSubset_chart V.index V.index V.domain V.domain Subset.rfl)
  have hV : V.locus ⊆ Set.range (B.atlas.chart V.index) :=
    B.atlas.domainSubset_chart V.index V.index V.domain V.domain Subset.rfl
  have he := e.hom.comp_chart V.index hD hV
  rw [B.atlas.domainChartRestriction_self V.index V.domain hV] at he
  exact he.trans (hf.domainImage_chartRestriction U V.index hD _)

/-- Descent to a recognized chart and its entire image retains the actual
inverse image-algebra comparison. -/
theorem saturationExtension_fullRecognitionPairs_pullback_recognizedImage
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (h : f.baseMap '' Set.range V.chart ⊆
      Set.range (hf.recognizedImage hc V).chart) :
    (f.saturationExtension hc).fullRecognitionPairs.pullback
      V (hf.recognizedImage hc V) h =
        (hf.recognizedImageEquiv hc V).symm.toBoundedAlgHom := by
  apply V.hom_ext
  intro s hs
  have hST : f.baseMap '' Set.range (A.atlas.saturatedAtlas.chart s) ⊆
      Set.range (B.atlas.saturatedAtlas.chart (hf.saturatedImageIndex s)) :=
    (hf.saturatedImage_range s).symm.subset
  rw [(f.saturationExtension hc).originalRestriction_comp_fullRecognitionPairs
    V (hf.recognizedImage hc V) h s hs (hf.saturatedImageIndex s)
      (hf.saturatedImage_subset_recognizedImage hc V s hs) hST,
    hf.saturationExtension_pullback_saturatedImage hc s hST]
  apply BoundedAlgHom.ext
  intro x
  apply (hf.saturatedImageEquiv s).injective
  have hn := congrArg
    (fun q : BoundedAlgHom K V.algebra
      (B.atlas.saturatedAtlas.algebra (hf.saturatedImageIndex s)) =>
        q ((hf.recognizedImageEquiv hc V).symm x))
    (hf.recognizedImageEquiv_originalRestriction hc V s hs)
  change (hf.saturatedImageEquiv s)
      ((hf.saturatedImageEquiv s).symm
        ((hf.recognizedImage hc V).originalRestriction (hf.saturatedImageIndex s)
          (hf.saturatedImage_subset_recognizedImage hc V s hs) x)) =
    (hf.saturatedImageEquiv s)
      (V.originalRestriction s hs ((hf.recognizedImageEquiv hc V).symm x))
  rw [(hf.saturatedImageEquiv s).apply_symm_apply]
  simpa only [recognitionImageChartDomain, BoundedAlgHom.comp_apply,
    BoundedAlgEquiv.toBoundedAlgHom_apply,
    BoundedAlgEquiv.apply_symm_apply] using hn


end IsDomainEmbedding
end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
