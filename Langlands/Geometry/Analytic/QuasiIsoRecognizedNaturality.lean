import Langlands.Geometry.Analytic.QuasiIsoReverseRecognition
import Langlands.Geometry.Analytic.FullRecognitionNaturality

/-! # Full bounded naturality of recognized images under coherent quasi-isomorphisms -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsQuasiIso

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K} {f : StrongHom A B}
  (hf : f.IsQuasiIso) (hc : f.HasCoherentPullbacks)

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

/-- The actual image algebra comparisons intertwine every recognized
restriction as equality of entire bounded algebra homomorphisms. -/
theorem recognizedImageEquiv_naturality
    (U V : A.atlas.saturatedAtlas.RecognizedSubset) (hUV : U.locus ⊆ V.locus) :
    (hf.recognizedImageEquiv hc U).toBoundedAlgHom.comp (U.restriction V hUV) =
      ((hf.recognizedImage hc U).restriction (hf.recognizedImage hc V)
        (by
          rw [hf.recognizedImage_locus, hf.recognizedImage_locus]
          exact Set.image_mono hUV)).comp
            (hf.recognizedImageEquiv hc V).toBoundedAlgHom := by
  let Y := hf.recognizedImage hc U
  let Z := hf.recognizedImage hc V
  let c := hf.recognitionImageAffinoidRealization hc U
  let hYZ : Y.locus ⊆ Z.locus :=
    (hf.recognizedImage_locus hc U).subset.trans
      ((Set.image_mono hUV).trans (hf.recognizedImage_locus hc V).symm.subset)
  ext x
  apply (hf.recognizedImageEquiv hc U).symm.injective
  apply c.domainCover.algebra_ext_of_restrict_eq
  intro i
  let s := U.property.cover.index i
  let hs := U.component_subset i
  let hsY := hf.saturatedImage_subset_recognizedImage hc U s hs
  have hU := hf.recognizedImageEquiv_originalRestriction hc U s hs
  have hV := hf.recognizedImageEquiv_originalRestriction hc V s (hs.trans hUV)
  have hO := hf.recognitionImageChartDomain_comp_restriction U V hUV s hs
  have hY := Y.originalRestriction_comp_restriction Z hYZ
    (hf.saturatedImageIndex s) hsY
  have hi (y : Y.algebra) :
      c.restriction i ((hf.recognizedImageEquiv hc U).symm y) =
        Y.originalRestriction (hf.saturatedImageIndex s) hsY y :=
    (congrArg
      (fun q : BoundedAlgHom K U.algebra
        (B.atlas.saturatedAtlas.algebra (hf.saturatedImageIndex s)) =>
          q ((hf.recognizedImageEquiv hc U).symm y)) hU).symm.trans
      (congrArg (Y.originalRestriction (hf.saturatedImageIndex s) hsY)
        ((hf.recognizedImageEquiv hc U).apply_symm_apply y))
  change c.restriction i
      ((hf.recognizedImageEquiv hc U).symm
        ((hf.recognizedImageEquiv hc U) (U.restriction V hUV x))) =
    c.restriction i
      ((hf.recognizedImageEquiv hc U).symm
        (Y.restriction Z hYZ ((hf.recognizedImageEquiv hc V) x)))
  rw [(hf.recognizedImageEquiv hc U).symm_apply_apply]
  exact (congrArg
    (fun q : BoundedAlgHom K V.algebra
      (B.atlas.saturatedAtlas.algebra (hf.saturatedImageIndex s)) => q x) hO).trans
    ((congrArg
      (fun q : BoundedAlgHom K V.algebra
        (B.atlas.saturatedAtlas.algebra (hf.saturatedImageIndex s)) => q x) hV).symm.trans
      ((congrArg
        (fun q : BoundedAlgHom K Z.algebra
          (B.atlas.saturatedAtlas.algebra (hf.saturatedImageIndex s)) =>
            q ((hf.recognizedImageEquiv hc V) x)) hY).symm.trans
        (hi (Y.restriction Z hYZ ((hf.recognizedImageEquiv hc V) x))).symm))

/-- The already constructed image functor's actual bounded restrictions
are intertwined by the original realization comparison equivalences. -/
theorem recognizedImageFunctor_naturality
    {U V : A.atlas.saturatedAtlas.RecognizedSubset} (p : U ⟶ V) :
    (hf.recognizedImageEquiv hc U).toBoundedAlgHom.comp p.restriction =
      ((hf.recognizedImageFunctor hc).map p).restriction.comp
        (hf.recognizedImageEquiv hc V).toBoundedAlgHom :=
  hf.recognizedImageEquiv_naturality hc U V p.subset

/-- Actual mutually inverse bounded algebra maps give the comparison of
each image affinoid presentation with its source presentation. -/
def recognizedImageAffinoidIso (V : A.atlas.saturatedAtlas.RecognizedSubset) :
    Opposite.op (hf.recognizedImage hc V).algebra ≅ Opposite.op V.algebra where
  hom := Quiver.Hom.op
    (show V.algebra ⟶ (hf.recognizedImage hc V).algebra from
      (hf.recognizedImageEquiv hc V).toBoundedAlgHom)
  inv := Quiver.Hom.op
    (show (hf.recognizedImage hc V).algebra ⟶ V.algebra from
      (hf.recognizedImageEquiv hc V).symm.toBoundedAlgHom)
  hom_inv_id := congrArg
    (fun q : (hf.recognizedImage hc V).algebra ⟶
      (hf.recognizedImage hc V).algebra => Quiver.Hom.op q)
    (BoundedAlgHom.ext fun x => (hf.recognizedImageEquiv hc V).apply_symm_apply x)
  inv_hom_id := congrArg (fun q : V.algebra ⟶ V.algebra => Quiver.Hom.op q)
    (BoundedAlgHom.ext fun x => (hf.recognizedImageEquiv hc V).symm_apply_apply x)

/-- The image functor identifies actual affinoid diagrams through the
full bounded naturality equations, without a target closure premise. -/
def recognizedImageAffinoidNatIso :
    hf.recognizedImageFunctor hc ⋙
        RecognizedSubset.toAffinoidSpace B.atlas.saturatedAtlas ≅
      RecognizedSubset.toAffinoidSpace A.atlas.saturatedAtlas :=
  NatIso.ofComponents (hf.recognizedImageAffinoidIso hc) (by
    intro U V p
    exact congrArg
      (fun q : V.algebra ⟶ (hf.recognizedImage hc U).algebra =>
        Quiver.Hom.op q)
      (hf.recognizedImageFunctor_naturality hc p).symm)

/-- The actual spectrum comparison lies over the original ambient
homeomorphism on every point of every recognized image. -/
theorem recognizedImageAffinoidNatIso_over_ambient
    (V : A.atlas.saturatedAtlas.RecognizedSubset)
    (x : BanachSpectrum (hf.recognizedImage hc V).algebra) :
    f.baseMap (V.chart ((affinoidSpectrumFunctor K).map
        ((hf.recognizedImageAffinoidNatIso hc).hom.app V) x)) =
      (hf.recognizedImage hc V).chart x :=
  (hf.recognizedImage_chart hc V x).symm

variable (hb : B.atlas.HasAllLocalDomains)

/-- The inverse forward comparison and actual target counit construct
the reverse affinoid comparison, including full bounded naturality. -/
def reverseRecognizedImageAffinoidNatIso :
    hf.reverseRecognizedImageFunctor hc hb ⋙
        RecognizedSubset.toAffinoidSpace A.atlas.saturatedAtlas ≅
      RecognizedSubset.toAffinoidSpace B.atlas.saturatedAtlas :=
  Functor.isoWhiskerLeft (hf.reverseRecognizedImageFunctor hc hb)
      (hf.recognizedImageAffinoidNatIso hc).symm ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (hf.recognizedImageCounitIso hc hb)
      (RecognizedSubset.toAffinoidSpace B.atlas.saturatedAtlas) ≪≫
    (RecognizedSubset.toAffinoidSpace B.atlas.saturatedAtlas).leftUnitor

/-- Extract both actual bounded inverse maps from the constructed reverse
natural isomorphism. This is a new, naturally chosen algebra comparison. -/
def reverseRecognizedImageNaturalEquiv
    (V : B.atlas.saturatedAtlas.RecognizedSubset) :
    BoundedAlgEquiv K V.algebra (hf.reverseRecognizedImage hc hb V).algebra := by
  let e := (hf.reverseRecognizedImageAffinoidNatIso hc hb).app V
  exact BoundedAlgEquiv.ofHomInv (Quiver.Hom.unop e.hom) (Quiver.Hom.unop e.inv)
    (fun b => congrArg
      (fun q : Opposite.op V.algebra ⟶ Opposite.op V.algebra =>
        BoundedAlgHom.toAlgHom (Quiver.Hom.unop q) b) e.inv_hom_id)
    (fun b => congrArg
      (fun q : Opposite.op (hf.reverseRecognizedImage hc hb V).algebra ⟶
        Opposite.op (hf.reverseRecognizedImage hc hb V).algebra =>
          BoundedAlgHom.toAlgHom (Quiver.Hom.unop q) b) e.hom_inv_id)

/-- Reverse naturality is equality of the entire bounded restriction maps. -/
theorem reverseRecognizedImageNaturalEquiv_naturality
    {U V : B.atlas.saturatedAtlas.RecognizedSubset} (p : U ⟶ V) :
    (hf.reverseRecognizedImageNaturalEquiv hc hb U).toBoundedAlgHom.comp p.restriction =
      ((hf.reverseRecognizedImageFunctor hc hb).map p).restriction.comp
        (hf.reverseRecognizedImageNaturalEquiv hc hb V).toBoundedAlgHom := by
  exact (congrArg
    (fun q : Opposite.op (hf.reverseRecognizedImage hc hb U).algebra ⟶
      Opposite.op V.algebra => Quiver.Hom.unop q)
    ((hf.reverseRecognizedImageAffinoidNatIso hc hb).hom.naturality p)).symm

/-- The reverse comparison lies over the same ambient homeomorphism,
with the spectrum direction determined by its bounded algebra map. -/
theorem reverseRecognizedImageAffinoidNatIso_over_ambient
    (V : B.atlas.saturatedAtlas.RecognizedSubset)
    (x : BanachSpectrum (hf.reverseRecognizedImage hc hb V).algebra) :
    V.chart ((affinoidSpectrumFunctor K).map
        ((hf.reverseRecognizedImageAffinoidNatIso hc hb).hom.app V) x) =
      f.baseMap ((hf.reverseRecognizedImage hc hb V).chart x) := by
  let W := hf.reverseRecognizedImage hc hb V
  let e := hf.recognizedImageEquiv hc W
  let y := e.spectrumHomeomorph.symm x
  change V.chart ((hf.recognizedImageCounitComponent hc hb V).hom.spectrumMap y) =
    f.baseMap (W.chart x)
  exact ((hf.recognizedImageCounitComponent hc hb V).hom.chart_naturality y).trans
    ((hf.recognizedImage_chart hc W y).trans
      (congrArg (fun z => f.baseMap (W.chart z))
        (e.spectrumHomeomorph.apply_symm_apply x)))

theorem reverseRecognizedImageNaturalEquiv_chart
    (V : B.atlas.saturatedAtlas.RecognizedSubset)
    (x : BanachSpectrum (hf.reverseRecognizedImage hc hb V).algebra) :
    (hf.reverseRecognizedImage hc hb V).chart x =
      hf.inverseBaseMap
        (V.chart ((hf.reverseRecognizedImageNaturalEquiv hc hb V).spectrumHomeomorph x)) := by
  apply hf.1.injective
  rw [hf.baseMap_inverseBaseMap]
  exact (hf.reverseRecognizedImageAffinoidNatIso_over_ambient hc hb V x).symm

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom.IsQuasiIso
