import Langlands.Geometry.Analytic.StrongLocalDomainInverseImage
import Langlands.Geometry.Analytic.CoherentStrongLocalDomain
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Full bounded naturality of actual local-domain inverse images -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K} (f : StrongHom A B)

private theorem localDomain_hom_eq {U V : LocalDomain A.atlas} (p q : U ⟶ V) :
    p = q :=
  @Subsingleton.elim (LocalDomain.Inclusion U V) inferInstance p q

/-- The actual inverse-image domain maps into the complete target local domain. -/
theorem localDomainInverseImage_image_subset (U : LocalDomain A.atlas)
    (V : LocalDomain B.atlas)
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart V.index)) :
    f.baseMap '' (f.localDomainInverseImage U V.index h V.domain).locus ⊆ V.locus := by
  rintro _ ⟨x, hx, rfl⟩
  exact ((f.localDomainInverseImage_locus U V.index h V.domain) ▸ hx).2

/-- Full-test uniqueness identifies the second pushout leg with the previously
constructed map to the unchanged target domain, under intrinsic coherence. -/
theorem localDomainInverseImageMap_eq_localDomainPullback
    (hf : f.HasCoherentPullbacks) (U : LocalDomain A.atlas)
    (V : LocalDomain B.atlas)
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart V.index)) :
    f.localDomainInverseImageMap U V.index h V.domain =
      f.localDomainPullback (f.localDomainInverseImage U V.index h V.domain) V
        (f.localDomainInverseImage_image_subset U V h) := by
  apply f.localDomainPullback_unique
  exact (f.localDomainInverseImageMap_comp_baseMap U V.index h V.domain).trans
    (f.localChartPullback_source hf
      (f.localDomainInverseImageInclusion U V.index h V.domain) V.index _ h)

/-- Both local-domain inclusions may cross original parent charts. -/
def localDomainInverseImageRestriction
    {U U' : LocalDomain A.atlas} {V V' : LocalDomain B.atlas}
    (p : U ⟶ U') (q : V ⟶ V')
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart V.index))
    (h' : f.baseMap '' U'.locus ⊆ Set.range (B.atlas.chart V'.index)) :
    f.localDomainInverseImage U V.index h V.domain ⟶
      f.localDomainInverseImage U' V'.index h' V'.domain :=
  LocalDomain.Inclusion.ofSubset _ _ (by
    rw [f.localDomainInverseImage_locus, f.localDomainInverseImage_locus]
    intro x hx
    exact ⟨p.subset hx.1, q.subset hx.2⟩)

/-- The comparison triangle consists of actual full-domain restrictions. -/
theorem localDomainInverseImageRestriction_source
    {U U' : LocalDomain A.atlas} {V V' : LocalDomain B.atlas}
    (p : U ⟶ U') (q : V ⟶ V')
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart V.index))
    (h' : f.baseMap '' U'.locus ⊆ Set.range (B.atlas.chart V'.index)) :
    f.localDomainInverseImageRestriction p q h h' ≫
        f.localDomainInverseImageInclusion U' V'.index h' V'.domain =
      f.localDomainInverseImageInclusion U V.index h V.domain ≫ p :=
  localDomain_hom_eq _ _

/-- The complete first-leg square, including both original source restrictions. -/
theorem localDomainInverseImageRestriction_comp_source
    {U U' : LocalDomain A.atlas} {V V' : LocalDomain B.atlas}
    (p : U ⟶ U') (q : V ⟶ V')
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart V.index))
    (h' : f.baseMap '' U'.locus ⊆ Set.range (B.atlas.chart V'.index)) :
    (f.localDomainInverseImageRestriction p q h h').restriction.comp
        (f.localDomainInverseImageInclusion U' V'.index h' V'.domain).restriction =
      (f.localDomainInverseImageInclusion U V.index h V.domain).restriction.comp
        p.restriction :=
  congrArg (fun r => r.restriction)
    (f.localDomainInverseImageRestriction_source p q h h')

/-- Coherence gives the complete second-leg square for arbitrary parents,
rather than only equality of induced maps on spectrum points. -/
theorem localDomainInverseImageRestriction_comp_target
    (hf : f.HasCoherentPullbacks)
    {U U' : LocalDomain A.atlas} {V V' : LocalDomain B.atlas}
    (p : U ⟶ U') (q : V ⟶ V')
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart V.index))
    (h' : f.baseMap '' U'.locus ⊆ Set.range (B.atlas.chart V'.index)) :
    (f.localDomainInverseImageRestriction p q h h').restriction.comp
        (f.localDomainInverseImageMap U' V'.index h' V'.domain) =
      (f.localDomainInverseImageMap U V.index h V.domain).comp q.restriction := by
  rw [f.localDomainInverseImageMap_eq_localDomainPullback hf,
    f.localDomainInverseImageMap_eq_localDomainPullback hf]
  exact f.localDomainPullback_naturality hf
    (f.localDomainInverseImageRestriction p q h h') q
    (f.localDomainInverseImage_image_subset U V h)
    (f.localDomainInverseImage_image_subset U' V' h')

/-- The domain pairs for which the target parent chart contains the source image. -/
def localInverseImageProperty :
    ObjectProperty (LocalDomain A.atlas × LocalDomain B.atlas) :=
  fun P => f.baseMap '' P.1.locus ⊆ Set.range (B.atlas.chart P.2.index)

/-- Morphisms retain both actual inclusions, with arbitrary original parents. -/
abbrev LocalInverseImageData := f.localInverseImageProperty.FullSubcategory

def localInverseImageSource : f.LocalInverseImageData ⥤ LocalDomain A.atlas where
  obj P := P.obj.1
  map p := p.hom.1

def localInverseImageTarget : f.LocalInverseImageData ⥤ LocalDomain B.atlas where
  obj P := P.obj.2
  map p := p.hom.2

/-- Actual inverse images form a functor in both source and target domains. -/
def localInverseImageFunctor : f.LocalInverseImageData ⥤ LocalDomain A.atlas where
  obj P := f.localDomainInverseImage P.obj.1 P.obj.2.index P.property P.obj.2.domain
  map p := f.localDomainInverseImageRestriction p.hom.1 p.hom.2 _ _
  map_id _ := localDomain_hom_eq _ _
  map_comp _ _ := localDomain_hom_eq _ _

@[simp]
theorem localInverseImageFunctor_obj (P : f.LocalInverseImageData) :
    f.localInverseImageFunctor.obj P =
      f.localDomainInverseImage P.obj.1 P.obj.2.index P.property P.obj.2.domain := rfl

theorem localInverseImageFunctor_locus (P : f.LocalInverseImageData) :
    (f.localInverseImageFunctor.obj P).locus =
      P.obj.1.locus ∩ f.baseMap ⁻¹' P.obj.2.locus :=
  f.localDomainInverseImage_locus _ _ _ _

/-- The first bounded legs are natural without a coherence premise. -/
def localInverseImageSourceInclusion :
    f.localInverseImageFunctor ⟶ f.localInverseImageSource where
  app P := f.localDomainInverseImageInclusion P.obj.1 P.obj.2.index P.property P.obj.2.domain
  naturality _ _ _ := localDomain_hom_eq _ _

/-- The second bounded legs give a natural transformation of actual affinoid
spaces, with complete bounded-map naturality under intrinsic coherence. -/
def localInverseImageTargetMap (hf : f.HasCoherentPullbacks) :
    f.localInverseImageFunctor ⋙ LocalDomain.toAffinoidSpace A.atlas ⟶
      f.localInverseImageTarget ⋙ LocalDomain.toAffinoidSpace B.atlas where
  app P := Quiver.Hom.op
    (f.localDomainInverseImageMap P.obj.1 P.obj.2.index P.property P.obj.2.domain)
  naturality _ _ p := congrArg Quiver.Hom.op
    (f.localDomainInverseImageRestriction_comp_target hf p.hom.1 p.hom.2 _ _)

/-- Equal ambient source and target loci yield actual bounded comparison
isomorphisms even when both parent charts change. -/
def localDomainInverseImageIso
    {U U' : LocalDomain A.atlas} {V V' : LocalDomain B.atlas}
    (hU : U.locus = U'.locus) (hV : V.locus = V'.locus)
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart V.index))
    (h' : f.baseMap '' U'.locus ⊆ Set.range (B.atlas.chart V'.index)) :
    f.localDomainInverseImage U V.index h V.domain ≅
      f.localDomainInverseImage U' V'.index h' V'.domain :=
  LocalDomain.isoOfLocusEq _ _ (by
    rw [f.localDomainInverseImage_locus, f.localDomainInverseImage_locus]
    change U.locus ∩ f.baseMap ⁻¹' V.locus = U'.locus ∩ f.baseMap ⁻¹' V'.locus
    rw [hU, hV])

/-- The forward comparison is exactly the functorial actual restriction. -/
theorem localDomainInverseImageIso_hom
    {U U' : LocalDomain A.atlas} {V V' : LocalDomain B.atlas}
    (hU : U.locus = U'.locus) (hV : V.locus = V'.locus)
    (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart V.index))
    (h' : f.baseMap '' U'.locus ⊆ Set.range (B.atlas.chart V'.index)) :
    (f.localDomainInverseImageIso hU hV h h').hom =
      f.localDomainInverseImageRestriction
        (LocalDomain.isoOfLocusEq U U' hU).hom
        (LocalDomain.isoOfLocusEq V V' hV).hom h h' :=
  localDomain_hom_eq _ _

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
