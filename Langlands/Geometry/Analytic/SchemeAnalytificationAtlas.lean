import Langlands.Geometry.Analytic.SchemeAnalytificationLocalCharts
import Langlands.Geometry.Analytic.SaturatedDomainPreimage

/-! # The affinoid atlas of the glued analytification of a scheme -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Topology
open Langlands.Analytic.AffineSchemeAnalytification
open AffineAnalytification IndexedAffinoidAtlas PresentedAffinoidAlgebra

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType f]

/-- The two gluing properties of the glued analytification used to build its atlas: the
canonical maps are open embeddings, and the images of two affine opens meet in the union of
the images of the affine opens contained in both. -/
structure OpenGluing : Prop where
  isOpenEmbedding : ∀ U : X.affineOpens, IsOpenEmbedding (ι K f U)
  range_inter : ∀ U V : X.affineOpens, Set.range (ι K f U) ∩ Set.range (ι K f V) =
    ⋃ (W : X.affineOpens) (_ : (W : X.Opens) ≤ (U : X.Opens) ⊓ V), Set.range (ι K f W)

namespace OpenGluing

variable {K f}

theorem injective (hg : OpenGluing K f) : ∀ U : X.affineOpens, Function.Injective (ι K f U) :=
  fun U => (hg.isOpenEmbedding U).injective

end OpenGluing

/-- The images in the glued analytification of all local charts. -/
def chartImages : Set (Set (Space K f)) :=
  Set.range (LocalChart.image (K := K) (f := f))

/-- A chosen local chart with a prescribed image. -/
def chartRep (T : chartImages K f) : LocalChart K f :=
  Classical.choose (Set.mem_range.mp T.2)

theorem chartRep_image (T : chartImages K f) : (chartRep K f T).image = T.1 :=
  Classical.choose_spec (Set.mem_range.mp T.2)

theorem range_chartRep (T : chartImages K f) : Set.range (chartRep K f T).chart = T.1 :=
  (chartRep K f T).range_chart.trans (chartRep_image K f T)

/-- The image of a chart of the saturated atlas of an affine open is a chart image. -/
theorem image_mem_chartImages (W : X.affineOpens)
    (S : (saturated K (chartPresentation K f W)).presentation.atlas.Index) :
    ι K f W '' Set.range ((saturated K (chartPresentation K f W)).presentation.atlas.chart S) ∈
      chartImages K f := by
  refine ⟨⟨W, (presentation K (chartPresentation K f W)).atlas.saturatedRepresentative S⟩, ?_⟩
  change ι K f W '' LocalDomain.locus _ = _
  rw [← LocalDomain.range_ambientMap]
  rfl

theorem image_mem_nhdsWithin_of_isOpenEmbedding {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {e : α → β} (he : IsOpenEmbedding e) {B : Set β} {A : Set α} {w : α}
    (hA : A ∈ 𝓝[e ⁻¹' B] w) : e '' A ∈ 𝓝[B] (e w) := by
  rw [mem_nhdsWithin] at hA ⊢
  obtain ⟨O, hO, hwO, hOA⟩ := hA
  refine ⟨e '' O, he.isOpenMap O hO, ⟨w, hwO, rfl⟩, ?_⟩
  rintro _ ⟨⟨v, hv, rfl⟩, hvB⟩
  exact ⟨v, hOA ⟨hv, hvB⟩, rfl⟩

variable {K f}

/-- The preimage in the analytification of a smaller affine open `W` of the image of a local
chart is an analytic domain of the saturated atlas of `W`. -/
theorem isOriginalChartDomain_preimage_image (hg : OpenGluing K f) (G : LocalChart K f)
    {W : X.affineOpens} (hW : (W : X.Opens) ≤ G.affineOpen) :
    (saturated K (chartPresentation K f W)).presentation.atlas.IsOriginalChartDomain
      (ι K f W ⁻¹' G.image) := by
  let i : (saturated K (chartPresentation K f G.affineOpen)).presentation.atlas.Index :=
    ⟨G.domain.locus, ⟨G.domain, rfl⟩⟩
  have h0 := AffinoidAtlasPresentation.StrongHom.isOriginalChartDomain_preimage
    (saturatedHom K (chartPresentation K f G.affineOpen) (chartPresentation K f W)
      (restriction f hW))
    (saturated K (chartPresentation K f W)).hasAllLocalDomains (OriginalChartDomain.ofChart i)
  have hc : ι K f W ⁻¹' G.image = (saturatedHom K (chartPresentation K f G.affineOpen)
      (chartPresentation K f W) (restriction f hW)).baseMap ⁻¹'
        (OriginalChartDomain.ofChart i).carrier := by
    ext v
    change ι K f W v ∈ G.image ↔ localMap K f hW v ∈
      Set.range ((presentation K (chartPresentation K f G.affineOpen)).atlas.saturatedChart i)
    rw [(presentation K (chartPresentation K f G.affineOpen)).atlas.range_saturatedChart i,
      ← ι_localMap K f hW v]
    constructor
    · rintro ⟨y, hy, hyv⟩
      rw [← hg.injective _ hyv]
      exact hy
    · intro hv
      exact ⟨_, hv, rfl⟩
  exact (congrArg _ hc).mpr h0

/-- The chart images form a net. -/
theorem isNet_chartImages (hg : OpenGluing K f) : AtlasTopology.IsNet (chartImages K f) := by
  refine ⟨fun z => ?_, ?_⟩
  · obtain ⟨U, y, rfl⟩ := exists_ι K f z
    obtain ⟨σ, hσf, hστ, hσy, hσn⟩ : ∃ σ : Set (Set (LocalSpace K f U)), σ.Finite ∧
        σ ⊆ Set.range (fun i => Set.range
          ((saturated K (chartPresentation K f U)).presentation.atlas.chart i)) ∧
        (∀ V ∈ σ, y ∈ V) ∧ ⋃₀ σ ∈ 𝓝 y :=
      (saturated K (chartPresentation K f U)).presentation.atlas.isNet_chartFamily.1 y
    refine ⟨Set.image (ι K f U) '' σ, hσf.image _, ?_, ?_, ?_⟩
    · rintro _ ⟨V, hV, rfl⟩
      obtain ⟨S, rfl⟩ := hστ hV
      exact image_mem_chartImages K f U S
    · rintro _ ⟨V, hV, rfl⟩
      exact ⟨y, hσy V hV, rfl⟩
    · rw [← Set.image_sUnion]
      exact (hg.isOpenEmbedding U).isOpenMap.image_mem_nhds hσn
  · rintro _ ⟨G₁, rfl⟩ _ ⟨G₂, rfl⟩
    apply (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mpr
    intro Y hY z hz
    rw [Set.mem_singleton_iff] at hY
    subst hY
    have hz' : z ∈ Set.range (ι K f G₁.affineOpen) ∩ Set.range (ι K f G₂.affineOpen) :=
      ⟨Set.image_subset_range _ _ hz.1, Set.image_subset_range _ _ hz.2⟩
    rw [hg.range_inter] at hz'
    simp only [Set.mem_iUnion] at hz'
    obtain ⟨W, hW, w, rfl⟩ := hz'
    have hW₁ : (W : X.Opens) ≤ G₁.affineOpen := hW.trans inf_le_left
    have hW₂ : (W : X.Opens) ≤ G₂.affineOpen := hW.trans inf_le_right
    have hE : (saturated K (chartPresentation K f W)).presentation.atlas.IsOriginalChartDomain
        (ι K f W ⁻¹' (G₁.image ∩ G₂.image)) :=
      (isOriginalChartDomain_preimage_image hg G₁ hW₁).inter _
        (isOriginalChartDomain_preimage_image hg G₂ hW₂)
    obtain ⟨σ, hσf, hστ, hσw, hσn⟩ : ∃ σ : Set (Set (LocalSpace K f W)), σ.Finite ∧
        σ ⊆ Set.range (fun i => Set.range
          ((saturated K (chartPresentation K f W)).presentation.atlas.chart i)) ∧
        (∀ V ∈ σ, V ⊆ ι K f W ⁻¹' (G₁.image ∩ G₂.image) ∧ w ∈ V) ∧
        ⋃₀ σ ∈ 𝓝[ι K f W ⁻¹' (G₁.image ∩ G₂.image)] w :=
      (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp hE _ (Set.mem_singleton _) w hz
    refine ⟨Set.image (ι K f W) '' σ, hσf.image _, ?_, ?_, ?_⟩
    · rintro _ ⟨V, hV, rfl⟩
      obtain ⟨S, rfl⟩ := hστ hV
      exact image_mem_chartImages K f W S
    · rintro _ ⟨V, hV, rfl⟩
      refine ⟨?_, ⟨w, (hσw V hV).2, rfl⟩⟩
      rintro _ ⟨v, hv, rfl⟩
      exact (hσw V hV).1 hv
    · rw [← Set.image_sUnion]
      exact image_mem_nhdsWithin_of_isOpenEmbedding (hg.isOpenEmbedding W) hσn

theorem locallyHausdorff (hg : OpenGluing K f) (z : Space K f) :
    ∃ U : Set (Space K f), U ∈ 𝓝 z ∧ T2Space U := by
  obtain ⟨V, y, rfl⟩ := exists_ι K f z
  exact ⟨Set.range (ι K f V), (hg.isOpenEmbedding V).isOpen_range.mem_nhds ⟨y, rfl⟩,
    (hg.isOpenEmbedding V).isEmbedding.toHomeomorph.t2Space⟩

theorem range_chartFamily :
    Set.range (fun T : chartImages K f => Set.range (chartRep K f T).chart) =
      chartImages K f := by
  ext V
  constructor
  · rintro ⟨T, rfl⟩
    show Set.range (chartRep K f T).chart ∈ chartImages K f
    rw [range_chartRep]
    exact T.2
  · intro hV
    exact ⟨⟨V, hV⟩, range_chartRep K f ⟨V, hV⟩⟩

/-- The affinoid atlas of the glued analytification: its charts are the images of all local
charts, with the cross-chart restrictions as bounded restriction maps. -/
def schemeAtlas (hg : OpenGluing K f) : IndexedAffinoidAtlas.{u, u, u} K (Space K f) where
  Index := chartImages K f
  algebra T := (chartRep K f T).algebra
  chart T := (chartRep K f T).chart
  isEmbedding_chart T := (chartRep K f T).isEmbedding_chart (hg.isOpenEmbedding _).isEmbedding
  chartDomain_injective S T h := Subtype.ext
    ((range_chartRep K f S).symm.trans (h.trans (range_chartRep K f T)))
  locallyHausdorff := locallyHausdorff hg
  isNet_chartFamily := by
    rw [range_chartFamily]
    exact isNet_chartImages hg
  restriction S T h := LocalChart.cross hg.injective (chartRep K f S) (chartRep K f T) (by
    rw [← LocalChart.range_chart, ← LocalChart.range_chart]
    exact h)
  restriction_chart S T h x := LocalChart.cross_chart hg.injective _ x
  restriction_universal S T h R φ hφ := LocalChart.cross_universal hg.injective _ R φ
    fun x => by
      rw [← LocalChart.range_chart]
      exact hφ x
  restriction_id S h := LocalChart.cross_self hg.injective _ _
  restriction_comp S T U hST hTU hSU := LocalChart.cross_trans hg.injective _ _ _

theorem schemeAtlas_hasAllLocalDomains (hg : OpenGluing K f) :
    (schemeAtlas hg).HasAllLocalDomains := by
  refine Set.Subset.antisymm ?_ (schemeAtlas hg).chartFamily_subset_localDomainFamily
  rintro _ ⟨L, rfl⟩
  let G := chartRep K f L.index
  let G' : LocalChart K f := ⟨G.affineOpen, G.domain.extend L.domain⟩
  refine ⟨⟨G'.image, ⟨G', rfl⟩⟩, (range_chartRep K f _).trans ?_⟩
  exact (congrArg (Set.image (ι K f G.affineOpen))
    (LocalDomain.extend_locus G.domain L.domain)).trans (Set.image_image _ _ _)

end Langlands.Analytic.SchemeAnalytification
