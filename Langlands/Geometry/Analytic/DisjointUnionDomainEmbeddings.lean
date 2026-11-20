import Langlands.Geometry.Analytic.LocalizedDisjointUnion
import Langlands.Geometry.Analytic.DomainEmbeddingRecognition
import Langlands.Geometry.Analytic.CompatibleStrongQuasiIsomorphisms

/-! # The inclusions of the pieces of a disjoint union are domain embeddings -/

noncomputable section

universe u v w z

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic

open Set Topology PresentedAffinoidAlgebra IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation.StrongHom.IsDomainEmbedding

variable {A B : AffinoidAtlasPresentation.{u, v, w} K} {f : StrongHom A B}

/-- The spectrum maps of the bounded pullbacks of an embedding are embeddings. -/
theorem isEmbedding_pullback (hf : f.IsDomainEmbedding) (i : A.atlas.Index)
    (j : B.atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    IsEmbedding (BanachSpectrum.comap (f.pullback i j h).toBoundedRingHom) := by
  apply (B.atlas.isEmbedding_chart j).of_comp_iff.mp
  have hsquare :
      B.atlas.chart j ∘ BanachSpectrum.comap (f.pullback i j h).toBoundedRingHom =
        f.baseMap ∘ A.atlas.chart i :=
    funext (f.chart_comm i j h)
  rw [hsquare]
  exact hf.1.comp (A.atlas.isEmbedding_chart i)

/-- Every constructed source-domain map to an original target chart represents the image of
the source domain when the original map is a domain embedding. -/
theorem represents_localChartPullback (hf : f.IsDomainEmbedding) (U : LocalDomain A.atlas)
    (j : B.atlas.Index) (h : f.baseMap '' U.locus ⊆ Set.range (B.atlas.chart j)) :
    Represents K (f.localChartPullback U j h)
      (B.atlas.chart j ⁻¹' (f.baseMap '' U.locus)) := by
  let k := f.chosenTargetIndex U.index
  have hparent := (hf.2 U.index k (f.chosenTarget_admissible U.index)).comp_of_injective
    U.domain.represents (hf.isEmbedding_pullback U.index k
      (f.chosenTarget_admissible U.index)).injective
  have himage : B.atlas.mapChartImage k U.algebra
      (f.mapAffinoidChart U.index k (f.chosenTarget_admissible U.index)
        U.algebra U.domain.baseMap) = f.baseMap '' U.locus := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      dsimp only
      rw [f.mapAffinoidChart_chart]
      exact ⟨U.ambientMap x,
        ⟨U.domain.spectrumMap x, U.domain.represents.hasImageIn x, rfl⟩, rfl⟩
    · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
      obtain ⟨t, ht⟩ := U.domain.represents.2.1.symm ▸ hz
      refine ⟨t, ?_⟩
      dsimp only
      rw [f.mapAffinoidChart_chart]
      exact congrArg f.baseMap (congrArg (A.atlas.chart U.index) ht)
  have hc := B.atlas.represents_changeMapChart k j U.algebra
    (f.mapAffinoidChart U.index k (f.chosenTarget_admissible U.index)
      U.algebra U.domain.baseMap) hparent (f.localDomain_parentPullback_image U j h)
  rw [himage] at hc
  exact hc

/-- Factoring through a target domain retains the representation of the image of the source
domain. -/
theorem represents_localDomainPullback (hf : f.IsDomainEmbedding) (U : LocalDomain A.atlas)
    (V : LocalDomain B.atlas) (h : f.baseMap '' U.locus ⊆ V.locus) :
    Represents K (f.localDomainPullback U V h)
      (V.ambientMap ⁻¹' (f.baseMap '' U.locus)) := by
  have hparent := hf.represents_localChartPullback U V.index
    (f.localDomain_parent_admissible U V h)
  rw [← f.localDomainPullback_comp_baseMap U V h] at hparent
  exact V.domain.represents.of_comp_of_injective hparent
    V.domain.spectrumMap_injective

/-- The extension of a domain embedding to the saturated atlases is a domain embedding. -/
theorem saturationExtension (hf : f.IsDomainEmbedding) (hc : f.HasCoherentPullbacks) :
    (f.saturationExtension hc).IsDomainEmbedding := by
  refine ⟨hf.1, ?_⟩
  intro S T h
  have hlocal : f.baseMap '' (A.atlas.saturatedRepresentative S).locus ⊆
      (B.atlas.saturatedRepresentative T).locus := by
    rw [← (A.atlas.saturatedRepresentative S).range_ambientMap,
      ← (B.atlas.saturatedRepresentative T).range_ambientMap]
    exact h
  change Represents K (f.localDomainPullback
    (A.atlas.saturatedRepresentative S) (B.atlas.saturatedRepresentative T) hlocal)
    ((B.atlas.saturatedRepresentative T).ambientMap ⁻¹'
      (f.baseMap '' Set.range (A.atlas.saturatedRepresentative S).ambientMap))
  rw [(A.atlas.saturatedRepresentative S).range_ambientMap]
  exact hf.represents_localDomainPullback (A.atlas.saturatedRepresentative S)
    (B.atlas.saturatedRepresentative T) hlocal

end AffinoidAtlasPresentation.StrongHom.IsDomainEmbedding

namespace AtlasDisjointUnion

open AffinoidAtlasPresentation

variable {I : Type z} (A : I → AffinoidAtlasPresentation.{u, max z v, max z w} K)
  (hA : ∀ i, (A i).atlas.HasNonemptyCharts)

/-- The strong inclusion of a component of a disjoint union is a domain embedding: its
pullbacks are restrictions of the disjoint-union atlas, which represent the images of the
component charts. -/
theorem isDomainEmbedding_inclusionStrong (i : I) :
    (inclusionStrong A hA i).IsDomainEmbedding := by
  refine ⟨by exact IsEmbedding.sigmaMk (σ := fun j => (A j).space), ?_⟩
  intro c d h
  have hl : (inclusionStrong A hA i).chartImageLocus c d =
      (presentation A hA).atlas.chart d ⁻¹'
        Set.range ((presentation A hA).atlas.chart ⟨i, c⟩) := by
    unfold StrongHom.chartImageLocus
    rw [← image_sigmaMk_range A hA i c]
    rfl
  rw [hl]
  exact (presentation A hA).atlas.restriction_represents ⟨i, c⟩ d
    (range_subset_of_image_subset A hA i c h)

end AtlasDisjointUnion

namespace SaturatedAtlasPresentation

variable {J : Type z}

/-- The saturated inclusions of the chosen disjoint union are domain embeddings. -/
theorem isDomainEmbedding_sigmaCofan_inj
    (T : J → SaturatedAtlasPresentation.{u, max z v, max z v} K) (j : J) :
    ((sigmaCofan T).inj j).IsDomainEmbedding :=
  (AtlasDisjointUnion.isDomainEmbedding_inclusionStrong (nonemptyFamily T)
    (nonemptyFamily_hasNonemptyCharts T) j).saturationExtension
    (AtlasDisjointUnion.compatibleInclusion (nonemptyFamily T)
      (nonemptyFamily_hasNonemptyCharts T) j).coherent

end SaturatedAtlasPresentation

end Langlands.Analytic
