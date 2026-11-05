import Langlands.Geometry.Analytic.CoherentStrongDomainPullback
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocalization
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainEmbeddedCoverLocalization

/-! # Actual inverse images inside source local affinoid domains -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  (f : StrongHom A B) (U : LocalDomain A.atlas) (j : B.atlas.Index)
  (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j))

/-- Pull back the target full domain along the constructed local bounded map,
then extend through the source domain without changing the pushout algebra. -/
def localDomainInverseImage (V : Domain K (B.atlas.algebra j)) :
    LocalDomain A.atlas :=
  ⟨U.index, U.domain.extend (Domain.pullback (f.localChartPullback U j h) V)⟩

@[simp]
theorem localDomainInverseImage_algebra (V : Domain K (B.atlas.algebra j)) :
    (f.localDomainInverseImage U j h V).algebra =
      AffinoidPushout.algebra (f.localChartPullback U j h) V.baseMap := rfl

/-- The exact image through the original source-domain embedding. -/
theorem localDomainInverseImage_locus_image (V : Domain K (B.atlas.algebra j)) :
    (f.localDomainInverseImage U j h V).locus =
      U.ambientMap '' (BanachSpectrum.comap (f.localChartPullback U j h).toBoundedRingHom
        ⁻¹' V.locus) := by
  change A.atlas.chart U.index '' (U.domain.spectrumMap '' _) = _
  rw [Set.image_image]
  rfl

/-- The actual quotient represents precisely the source-domain part of the
ambient inverse image, even when the entire source chart does not map into j. -/
theorem localDomainInverseImage_locus (V : Domain K (B.atlas.algebra j)) :
    (f.localDomainInverseImage U j h V).locus =
      U.locus ∩ f.baseMap ⁻¹' (B.atlas.chart j '' V.locus) := by
  rw [f.localDomainInverseImage_locus_image]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨U.range_ambientMap ▸ Set.mem_range_self y, ?_⟩
    exact ⟨BanachSpectrum.comap (f.localChartPullback U j h).toBoundedRingHom y,
      hy, f.localChartPullback_chart U j h y⟩
  · rintro ⟨hx, z, hz, hzx⟩
    obtain ⟨y, rfl⟩ := U.range_ambientMap.symm ▸ hx
    refine ⟨y, ?_, rfl⟩
    have heq := (B.atlas.isEmbedding_chart j).injective
      ((f.localChartPullback_chart U j h y).trans hzx.symm)
    change BanachSpectrum.comap (f.localChartPullback U j h).toBoundedRingHom y ∈ V.locus
    exact heq.symm ▸ hz

/-- The unchanged first quotient leg is the actual restriction into U. -/
def localDomainInverseImageInclusion (V : Domain K (B.atlas.algebra j)) :
    f.localDomainInverseImage U j h V ⟶ U :=
  (LocalDomain.sameChartFunctor A.atlas U.index).map
    (U.domain.extendInclusion (Domain.pullback (f.localChartPullback U j h) V))

@[simp]
theorem localDomainInverseImageInclusion_restriction
    (V : Domain K (B.atlas.algebra j)) :
    (f.localDomainInverseImageInclusion U j h V).restriction =
      (Domain.pullback (f.localChartPullback U j h) V).baseMap := rfl

/-- The second actual quotient leg is the bounded map from the target domain. -/
def localDomainInverseImageMap (V : Domain K (B.atlas.algebra j)) :
    BoundedAlgHom K V.algebra (f.localDomainInverseImage U j h V).algebra :=
  Domain.pullbackMap (f.localChartPullback U j h) V

theorem localDomainInverseImageMap_comp_baseMap
    (V : Domain K (B.atlas.algebra j)) :
    (f.localDomainInverseImageMap U j h V).comp V.baseMap =
      (f.localDomainInverseImageInclusion U j h V).restriction.comp
        (f.localChartPullback U j h) :=
  Domain.pullbackMap_comp_baseMap (f.localChartPullback U j h) V

theorem localDomainInverseImage_ambientMap (V : Domain K (B.atlas.algebra j))
    (x : BanachSpectrum (f.localDomainInverseImage U j h V).algebra) :
    (f.localDomainInverseImage U j h V).ambientMap x =
      U.ambientMap
        ((Domain.pullback (f.localChartPullback U j h) V).spectrumMap x) := by
  exact congrArg (A.atlas.chart U.index)
    (U.domain.extend_spectrumMap (Domain.pullback (f.localChartPullback U j h) V) x)

/-- The actual continuous spectrum maps retain the ambient square for f. -/
theorem localDomainInverseImageMap_chart (V : Domain K (B.atlas.algebra j))
    (x : BanachSpectrum (f.localDomainInverseImage U j h V).algebra) :
    (⟨j, V⟩ : LocalDomain B.atlas).ambientMap
        (BanachSpectrum.comap (f.localDomainInverseImageMap U j h V).toBoundedRingHom x) =
      f.baseMap ((f.localDomainInverseImage U j h V).ambientMap x) := by
  exact (congrArg (B.atlas.chart j)
    (Domain.pullbackSpectrumMap_over_base (f.localChartPullback U j h) V x)).trans
      ((f.localChartPullback_chart U j h
        ((Domain.pullback (f.localChartPullback U j h) V).spectrumMap x)).trans
          (congrArg f.baseMap (f.localDomainInverseImage_ambientMap U j h V x).symm))

/-- Pullback followed by actual domain extension retains every bounded
restriction, with the source and target quotient squares. -/
def localDomainInverseImageFunctor :
    Domain K (B.atlas.algebra j) ⥤ LocalDomain A.atlas :=
  Domain.pullbackFunctor (f.localChartPullback U j h) ⋙
    U.domain.extendFunctor ⋙ LocalDomain.sameChartFunctor A.atlas U.index

@[simp]
theorem localDomainInverseImageFunctor_obj (V : Domain K (B.atlas.algebra j)) :
    (f.localDomainInverseImageFunctor U j h).obj V =
      f.localDomainInverseImage U j h V := rfl

@[simp]
theorem localDomainInverseImageFunctor_map_restriction
    {V W : Domain K (B.atlas.algebra j)} (p : V ⟶ W) :
    ((f.localDomainInverseImageFunctor U j h).map p).restriction =
      (Domain.pullbackRestriction (f.localChartPullback U j h) p).restriction := rfl

theorem localDomainInverseImageFunctor_map_comp_target
    {V W : Domain K (B.atlas.algebra j)} (p : V ⟶ W) :
    ((f.localDomainInverseImageFunctor U j h).map p).restriction.comp
        (f.localDomainInverseImageMap U j h W) =
      (f.localDomainInverseImageMap U j h V).comp p.restriction :=
  Domain.pullbackRestriction_comp_pullbackMap (f.localChartPullback U j h) p

/-- Finite target covers give finite actual full-domain covers in the source
parent chart, retaining their index and every changed bounded restriction. -/
def localDomainInverseImageCover {V : Domain K (B.atlas.algebra j)}
    (c : Domain.FiniteCover V) :
    Domain.FiniteCover (f.localDomainInverseImage U j h V).domain :=
  U.domain.extendFiniteCoverOfInjective U.domain.spectrumMap_injective
    (c.pullback (f.localChartPullback U j h))

@[simp]
theorem localDomainInverseImageCover_size {V : Domain K (B.atlas.algebra j)}
    (c : Domain.FiniteCover V) :
    (f.localDomainInverseImageCover U j h c).size = c.size := rfl

@[simp]
theorem localDomainInverseImageCover_obj {V : Domain K (B.atlas.algebra j)}
    (c : Domain.FiniteCover V) (t : Fin c.size) :
    (f.localDomainInverseImageCover U j h c).obj t =
      (f.localDomainInverseImage U j h (c.obj t)).domain := rfl

@[simp]
theorem localDomainInverseImageCover_map_restriction
    {V : Domain K (B.atlas.algebra j)} (c : Domain.FiniteCover V) (t : Fin c.size) :
    ((f.localDomainInverseImageCover U j h c).map t).restriction =
      ((f.localDomainInverseImageFunctor U j h).map (c.map t)).restriction := rfl

/-- The resulting actual inverse-image pieces cover the entire inverse image
inside U in the ambient source space. -/
theorem localDomainInverseImageCover_covers
    {V : Domain K (B.atlas.algebra j)} (c : Domain.FiniteCover V)
    {x : A.space} (hx : x ∈ (f.localDomainInverseImage U j h V).locus) :
    ∃ t : Fin c.size, x ∈ (f.localDomainInverseImage U j h (c.obj t)).locus := by
  obtain ⟨y, hy, rfl⟩ := hx
  obtain ⟨t, ht⟩ := (f.localDomainInverseImageCover U j h c).covers y hy
  exact ⟨t, y, ht, rfl⟩

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom
