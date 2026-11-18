import Langlands.Geometry.Analytic.SchemeAnalytificationAtlas
import Langlands.Geometry.Analytic.InvariantAnalyticDomains
import Langlands.Geometry.Analytic.SchemeAnalytificationAnalyticStructureStatement
import Langlands.Geometry.Analytic.SchemeAnalytificationGluingStatement

/-! # The analytic structure of the glued analytification of a scheme -/

noncomputable section

universe u

namespace Langlands.Analytic.SchemeAnalytification

open CategoryTheory _root_.AlgebraicGeometry Topology SaturatedAtlasPresentation
open Langlands.Analytic.AffineSchemeAnalytification
open AffineAnalytification IndexedAffinoidAtlas PresentedAffinoidAlgebra

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of K)} [LocallyOfFiniteType f]

theorem comp_pullback {A B C : SaturatedAtlasPresentation.{u, u, u} K} (φ : A ⟶ B) (ψ : B ⟶ C)
    (i : A.presentation.atlas.Index) (j : B.presentation.atlas.Index)
    (k : C.presentation.atlas.Index)
    (hφ : φ.baseMap '' Set.range (A.presentation.atlas.chart i) ⊆
      Set.range (B.presentation.atlas.chart j))
    (hψ : ψ.baseMap '' Set.range (B.presentation.atlas.chart j) ⊆
      Set.range (C.presentation.atlas.chart k))
    (h : (φ ≫ ψ).baseMap '' Set.range (A.presentation.atlas.chart i) ⊆
      Set.range (C.presentation.atlas.chart k)) :
    (φ ≫ ψ).pullback i k h = (φ.pullback i j hφ).comp (ψ.pullback j k hψ) :=
  AffinoidAtlasPresentation.StrongHom.saturatedComp_pullback φ ψ _ _ i j k hφ hψ h

variable (hg : OpenGluing K f)

/-- The glued analytification with the atlas of images of local charts. -/
def schemePresentation : SaturatedAtlasPresentation.{u, u, u} K where
  presentation := ⟨TopCat.of (Space K f), schemeAtlas hg⟩
  hasAllLocalDomains := schemeAtlas_hasAllLocalDomains hg

/-- The image of the analytification of an affine open, as an analytic domain. -/
def affineDomain (U : X.affineOpens) : (schemePresentation hg).AnalyticDomain :=
  ⟨Set.range (ι K f U), (schemeAtlas_hasAllLocalDomains hg).isOriginalChartDomain_of_isOpen
    (hg.isOpenEmbedding U).isOpen_range⟩

variable (K f) in
/-- The local chart given by a chart of the saturated atlas of an affine open. -/
def satChart (U : X.affineOpens)
    (i : (saturated K (chartPresentation K f U)).presentation.atlas.Index) : LocalChart K f :=
  ⟨U, (presentation K (chartPresentation K f U)).atlas.saturatedRepresentative i⟩

theorem satChart_image (U : X.affineOpens)
    (i : (saturated K (chartPresentation K f U)).presentation.atlas.Index) :
    (satChart K f U i).image =
      ι K f U '' Set.range ((saturated K (chartPresentation K f U)).presentation.atlas.chart i) :=
  congrArg (Set.image (ι K f U))
    ((presentation K (chartPresentation K f U)).atlas.saturatedRepresentative i).range_ambientMap.symm

/-- The chart of the glued atlas with the image of a saturated chart of an affine open. -/
def satIndex (U : X.affineOpens)
    (i : (saturated K (chartPresentation K f U)).presentation.atlas.Index) :
    (schemeAtlas hg).Index :=
  ⟨(satChart K f U i).image, ⟨_, rfl⟩⟩

theorem range_chart_satIndex (U : X.affineOpens)
    (i : (saturated K (chartPresentation K f U)).presentation.atlas.Index) :
    Set.range ((schemeAtlas hg).chart (satIndex hg U i)) = (satChart K f U i).image :=
  range_chartRep K f _

/-- The analytification of an affine open onto the image of its canonical map. -/
def toDomainBase (U : X.affineOpens) :
    C((saturated K (chartPresentation K f U)).presentation.space,
      ((schemePresentation hg).domain (affineDomain hg U)).presentation.space) :=
  ⟨fun y => ⟨ι K f U y, Set.mem_range_self y⟩, (ι K f U).continuous.subtype_mk _⟩

theorem image_subset_of_admissible (U : X.affineOpens)
    (i : (saturated K (chartPresentation K f U)).presentation.atlas.Index)
    (j : ((schemePresentation hg).domain (affineDomain hg U)).presentation.atlas.Index)
    (h : toDomainBase hg U '' Set.range ((saturated K (chartPresentation K f U)).presentation.atlas.chart i) ⊆
      Set.range (((schemePresentation hg).domain (affineDomain hg U)).presentation.atlas.chart j)) :
    (satChart K f U i).image ⊆ (chartRep K f j.val).image := by
  rw [satChart_image, ← LocalChart.range_chart]
  rintro _ ⟨y, hy, rfl⟩
  obtain ⟨x, hx⟩ := h ⟨y, hy, rfl⟩
  exact ⟨x, congrArg Subtype.val hx⟩

theorem admissible_of_image_subset (U : X.affineOpens)
    (i : (saturated K (chartPresentation K f U)).presentation.atlas.Index)
    (j : ((schemePresentation hg).domain (affineDomain hg U)).presentation.atlas.Index)
    (h : (satChart K f U i).image ⊆ (chartRep K f j.val).image) :
    toDomainBase hg U '' Set.range ((saturated K (chartPresentation K f U)).presentation.atlas.chart i) ⊆
      Set.range (((schemePresentation hg).domain (affineDomain hg U)).presentation.atlas.chart j) := by
  rintro _ ⟨y, hy, rfl⟩
  have hz : ι K f U y ∈ (chartRep K f j.val).image := h (by
    rw [satChart_image]
    exact ⟨y, hy, rfl⟩)
  rw [← LocalChart.range_chart] at hz
  obtain ⟨x, hx⟩ := hz
  exact ⟨x, Subtype.ext hx⟩

theorem image_subset_of_chart_subset (U : X.affineOpens)
    (j j' : ((schemePresentation hg).domain (affineDomain hg U)).presentation.atlas.Index)
    (hj : Set.range (((schemePresentation hg).domain (affineDomain hg U)).presentation.atlas.chart j) ⊆
      Set.range (((schemePresentation hg).domain (affineDomain hg U)).presentation.atlas.chart j')) :
    (chartRep K f j.val).image ⊆ (chartRep K f j'.val).image := by
  intro z hz
  rw [← LocalChart.range_chart] at hz ⊢
  exact (schemeAtlas hg).chart_subset_of_subspaceSubset _ j j' hj hz

/-- The canonical chart of the domain of an affine open containing a saturated chart. -/
def satDomainIndex (U : X.affineOpens)
    (i : (saturated K (chartPresentation K f U)).presentation.atlas.Index) :
    ((schemePresentation hg).domain (affineDomain hg U)).presentation.atlas.Index :=
  ⟨satIndex hg U i, (range_chart_satIndex hg U i).subset.trans (Set.image_subset_range _ _)⟩

/-- The strong map from the saturated analytification of an affine open to its image in the
glued analytification, with the cross-chart restrictions as bounded pullbacks. -/
def toDomainStrong (U : X.affineOpens) :
    AffinoidAtlasPresentation.StrongHom (saturated K (chartPresentation K f U)).presentation
      ((schemePresentation hg).domain (affineDomain hg U)).presentation where
  baseMap := toDomainBase hg U
  target_exists i := ⟨satDomainIndex hg U i, admissible_of_image_subset hg U i _
    (chartRep_image K f (satIndex hg U i)).symm.subset⟩
  pullback i j h := LocalChart.cross hg.injective (satChart K f U i) (chartRep K f j.val)
    (image_subset_of_admissible hg U i j h)
  chart_comm i j h x := Subtype.ext
    (LocalChart.cross_chart hg.injective (image_subset_of_admissible hg U i j h) x)
  restriction_comm i i' j j' _ hj h h' :=
    LocalChart.compatible_unique
      ((LocalChart.compatible_inclusion _).comp
        (LocalChart.cross_compatible hg.injective (image_subset_of_admissible hg U i' j' h')))
      ((LocalChart.cross_compatible hg.injective (image_subset_of_admissible hg U i j h)).comp
        (LocalChart.cross_compatible hg.injective (image_subset_of_chart_subset hg U j j' hj)))

/-- The morphism of saturated presentations from the analytification of an affine open to its
image in the glued analytification. -/
def toDomain (U : X.affineOpens) :
    saturated K (chartPresentation K f U) ⟶ (schemePresentation hg).domain (affineDomain hg U) :=
  toDomainStrong hg U

theorem toDomain_isQuasiIso (U : X.affineOpens) :
    AffinoidAtlasPresentation.StrongHom.IsQuasiIso (toDomainStrong hg U) := by
  refine ⟨isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(hg.isOpenEmbedding U).isEmbedding.codRestrict _ _, ?_⟩, fun i j h => ?_⟩
  · rintro ⟨_, y, rfl⟩
    exact ⟨y, rfl⟩
  have e : (toDomainStrong hg U).chartImageLocus i j =
      (chartRep K f j.val).chart ⁻¹' (satChart K f U i).image := by
    ext x
    unfold AffinoidAtlasPresentation.StrongHom.chartImageLocus
    constructor
    · rintro ⟨y, hy, hyx⟩
      show (chartRep K f j.val).chart x ∈ (satChart K f U i).image
      rw [satChart_image]
      exact ⟨y, hy, congrArg Subtype.val hyx⟩
    · intro hx
      change (chartRep K f j.val).chart x ∈ (satChart K f U i).image at hx
      rw [satChart_image] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      exact ⟨y, hy, Subtype.ext hyx⟩
  exact (congrArg _ e).mpr
    (LocalChart.represents_cross hg.injective (image_subset_of_admissible hg U i j h))

/-- The isomorphism in the localized category from the analytification of an affine open to its
image in the glued analytification. -/
def affineIso (U : X.affineOpens) :
    AffineAnalytification.localized K (chartPresentation K f U) ≅
      localizationFunctor.obj ((schemePresentation hg).domain (affineDomain hg U)) :=
  localizedQuasiIso (toDomain hg U) (toDomain_isQuasiIso hg U)

theorem toDomain_comp_inclusion_baseMap (U : X.affineOpens) (y : LocalSpace K f U) :
    (toDomain hg U ≫ (schemePresentation hg).domainInclusion (affineDomain hg U)).baseMap y =
      ι K f U y :=
  rfl

theorem toDomain_pullback (U : X.affineOpens)
    (i : (saturated K (chartPresentation K f U)).presentation.atlas.Index)
    (j : ((schemePresentation hg).domain (affineDomain hg U)).presentation.atlas.Index)
    (h : (toDomain hg U).baseMap ''
        Set.range ((saturated K (chartPresentation K f U)).presentation.atlas.chart i) ⊆
      Set.range (((schemePresentation hg).domain (affineDomain hg U)).presentation.atlas.chart j)) :
    LocalChart.Compatible (satChart K f U i) (chartRep K f j.val) ((toDomain hg U).pullback i j h) :=
  LocalChart.cross_compatible hg.injective (image_subset_of_admissible hg U i j h)

theorem domainInclusion_image_subset (U : X.affineOpens)
    (c : ((schemePresentation hg).domain (affineDomain hg U)).presentation.atlas.Index)
    (k : (schemePresentation hg).presentation.atlas.Index)
    (h : ((schemePresentation hg).domainInclusion (affineDomain hg U)).baseMap ''
        Set.range (((schemePresentation hg).domain (affineDomain hg U)).presentation.atlas.chart c) ⊆
      Set.range ((schemePresentation hg).presentation.atlas.chart k)) :
    (chartRep K f c.val).image ⊆ (chartRep K f k).image := by
  intro z hz
  rw [← LocalChart.range_chart] at hz ⊢
  obtain ⟨x, rfl⟩ := hz
  exact h ⟨_, ⟨x, rfl⟩, rfl⟩

theorem domainInclusion_pullback (U : X.affineOpens)
    (c : ((schemePresentation hg).domain (affineDomain hg U)).presentation.atlas.Index)
    (k : (schemePresentation hg).presentation.atlas.Index)
    (h : ((schemePresentation hg).domainInclusion (affineDomain hg U)).baseMap ''
        Set.range (((schemePresentation hg).domain (affineDomain hg U)).presentation.atlas.chart c) ⊆
      Set.range ((schemePresentation hg).presentation.atlas.chart k)) :
    LocalChart.Compatible (chartRep K f c.val) (chartRep K f k)
      (((schemePresentation hg).domainInclusion (affineDomain hg U)).pullback c k h) :=
  LocalChart.cross_compatible hg.injective (domainInclusion_image_subset hg U c k h)

/-- Compatibility with the restriction from an affine open to a smaller one, before
localization. -/
theorem saturatedHom_comp_toDomain {U V : X.affineOpens} (h : (V : X.Opens) ≤ U) :
    saturatedHom K (chartPresentation K f U) (chartPresentation K f V) (restriction f h) ≫
        toDomain hg U ≫ (schemePresentation hg).domainInclusion (affineDomain hg U) =
      toDomain hg V ≫ (schemePresentation hg).domainInclusion (affineDomain hg V) := by
  have hb : (saturatedHom K (chartPresentation K f U) (chartPresentation K f V)
        (restriction f h) ≫ toDomain hg U ≫
          (schemePresentation hg).domainInclusion (affineDomain hg U)).baseMap =
      (toDomain hg V ≫ (schemePresentation hg).domainInclusion (affineDomain hg V)).baseMap := by
    ext y
    rw [baseMap_comp, ContinuousMap.comp_apply, saturatedHom_baseMap]
    exact (toDomain_comp_inclusion_baseMap hg U (localMap K f h y)).trans
      ((ι_localMap K f h y).trans (toDomain_comp_inclusion_baseMap hg V y).symm)
  refine AffinoidAtlasPresentation.StrongHom.ext_of_saturated
    (saturated K (chartPresentation K f V)).hasAllLocalDomains hb fun i => ?_
  obtain ⟨j₁, hj₁⟩ := (saturatedHom K (chartPresentation K f U) (chartPresentation K f V)
    (restriction f h)).target_exists i
  let k := satIndex hg U j₁
  have hj₁' := hj₁
  rw [saturatedHom_baseMap] at hj₁'
  have hsub : (satChart K f V i).image ⊆ (satChart K f U j₁).image := by
    rw [satChart_image, satChart_image]
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨localMap K f h y, hj₁' ⟨y, hy, rfl⟩, ι_localMap K f h y⟩
  have hk : (saturatedHom K (chartPresentation K f U) (chartPresentation K f V)
        (restriction f h) ≫ toDomain hg U ≫
          (schemePresentation hg).domainInclusion (affineDomain hg U)).baseMap ''
        Set.range ((saturated K (chartPresentation K f V)).presentation.atlas.chart i) ⊆
      Set.range ((schemePresentation hg).presentation.atlas.chart k) := by
    rw [hb]
    rintro _ ⟨y, hy, rfl⟩
    change ι K f V y ∈ Set.range ((schemeAtlas hg).chart k)
    rw [range_chart_satIndex]
    apply hsub
    rw [satChart_image]
    exact ⟨y, hy, rfl⟩
  refine ⟨k, hk, ?_⟩
  have hk₁ : (toDomain hg U ≫ (schemePresentation hg).domainInclusion (affineDomain hg U)).baseMap ''
        Set.range ((saturated K (chartPresentation K f U)).presentation.atlas.chart j₁) ⊆
      Set.range ((schemePresentation hg).presentation.atlas.chart k) := by
    rintro _ ⟨y, hy, rfl⟩
    change ι K f U y ∈ Set.range ((schemeAtlas hg).chart k)
    rw [range_chart_satIndex, satChart_image]
    exact ⟨y, hy, rfl⟩
  have hm₁ := (toDomainStrong hg U).target_exists j₁
  have hm₁' : (toDomain hg U).baseMap ''
        Set.range ((saturated K (chartPresentation K f U)).presentation.atlas.chart j₁) ⊆
      Set.range (((schemePresentation hg).domain (affineDomain hg U)).presentation.atlas.chart
        (satDomainIndex hg U j₁)) :=
    admissible_of_image_subset hg U j₁ _ (chartRep_image K f (satIndex hg U j₁)).symm.subset
  have hinc₁ : ((schemePresentation hg).domainInclusion (affineDomain hg U)).baseMap ''
        Set.range (((schemePresentation hg).domain (affineDomain hg U)).presentation.atlas.chart
          (satDomainIndex hg U j₁)) ⊆
      Set.range ((schemePresentation hg).presentation.atlas.chart k) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  have hm₂' : (toDomain hg V).baseMap ''
        Set.range ((saturated K (chartPresentation K f V)).presentation.atlas.chart i) ⊆
      Set.range (((schemePresentation hg).domain (affineDomain hg V)).presentation.atlas.chart
        (satDomainIndex hg V i)) :=
    admissible_of_image_subset hg V i _ (chartRep_image K f (satIndex hg V i)).symm.subset
  have hinc₂ : ((schemePresentation hg).domainInclusion (affineDomain hg V)).baseMap ''
        Set.range (((schemePresentation hg).domain (affineDomain hg V)).presentation.atlas.chart
          (satDomainIndex hg V i)) ⊆
      Set.range ((schemePresentation hg).presentation.atlas.chart k) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    change (chartRep K f (satIndex hg V i)).chart x ∈ Set.range ((schemeAtlas hg).chart k)
    rw [range_chart_satIndex]
    exact hsub ((chartRep_image K f (satIndex hg V i)).subset (LocalChart.chart_mem_image _ x))
  clear hm₁
  have hk' : (toDomain hg V ≫ (schemePresentation hg).domainInclusion (affineDomain hg V)).baseMap ''
        Set.range ((saturated K (chartPresentation K f V)).presentation.atlas.chart i) ⊆
      Set.range ((schemePresentation hg).presentation.atlas.chart k) := by
    rw [← hb]
    exact hk
  have e1 := comp_pullback (saturatedHom K (chartPresentation K f U) (chartPresentation K f V)
    (restriction f h)) (toDomain hg U ≫ (schemePresentation hg).domainInclusion (affineDomain hg U))
    i j₁ k hj₁ hk₁ hk
  have e2 := comp_pullback (toDomain hg U)
    ((schemePresentation hg).domainInclusion (affineDomain hg U))
    j₁ (satDomainIndex hg U j₁) k hm₁' hinc₁ hk₁
  have e3 := comp_pullback (toDomain hg V)
    ((schemePresentation hg).domainInclusion (affineDomain hg V))
    i (satDomainIndex hg V i) k hm₂' hinc₂ hk'
  have hL := (LocalChart.compatible_saturatedHom h i j₁ hj₁).comp
    ((toDomain_pullback hg U j₁ _ hm₁').comp (domainInclusion_pullback hg U _ k hinc₁))
  have hR := (toDomain_pullback hg V i _ hm₂').comp (domainInclusion_pullback hg V _ k hinc₂)
  exact e1.trans ((congrArg (BoundedAlgHom.comp ((saturatedHom K (chartPresentation K f U)
    (chartPresentation K f V) (restriction f h)).pullback i j₁ hj₁)) e2).trans
      ((LocalChart.compatible_unique hL hR).trans e3.symm))

include hg in
/-- The glued analytification carries an analytic structure glued from the affine
analytifications, provided the canonical maps form an open gluing. -/
theorem analyticStructure_of_openGluing :
    ∃ (S : SaturatedAtlasPresentation.{u, u, u} K) (e : S.presentation.space ≃ₜ Space K f)
      (D : X.affineOpens → S.AnalyticDomain)
      (φ : ∀ U : X.affineOpens, AffineAnalytification.localized K (chartPresentation K f U) ≅
        localizationFunctor.obj (S.domain (D U))),
      (∀ U : X.affineOpens, e '' (D U).carrier = Set.range (ι K f U)) ∧
      (∀ (U : X.affineOpens) (y : LocalSpace K f U),
        e (localizedSpaceFunctor.map ((φ U).hom ≫ S.localizedDomainInclusion (D U)) y) =
          ι K f U y) ∧
      ∀ (U V : X.affineOpens) (h : (V : X.Opens) ≤ U),
        AffineAnalytification.localizedHom K (chartPresentation K f U)
            (chartPresentation K f V) (restriction f h) ≫
          (φ U).hom ≫ S.localizedDomainInclusion (D U) =
        (φ V).hom ≫ S.localizedDomainInclusion (D V) := by
  refine ⟨schemePresentation hg, Homeomorph.refl _, affineDomain hg, affineIso hg,
    fun U => Set.image_id _, fun U y => ?_, fun U V h => ?_⟩
  · change localizedSpaceFunctor.map (localizationFunctor.map (toDomain hg U) ≫
      localizationFunctor.map ((schemePresentation hg).domainInclusion (affineDomain hg U))) y = _
    rw [← Functor.map_comp, localizedSpaceFunctor_map]
    rfl
  · change localizationFunctor.map (saturatedHom K (chartPresentation K f U)
        (chartPresentation K f V) (restriction f h)) ≫
        localizationFunctor.map (toDomain hg U) ≫
          localizationFunctor.map ((schemePresentation hg).domainInclusion (affineDomain hg U)) =
      localizationFunctor.map (toDomain hg V) ≫
        localizationFunctor.map ((schemePresentation hg).domainInclusion (affineDomain hg V))
    rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
      saturatedHom_comp_toDomain hg h]

end Langlands.Analytic.SchemeAnalytification

namespace Langlands.Analytic.SchemeAnalytification

/-- The analytic structure statement follows from the gluing statement. -/
theorem schemeAnalytificationAnalyticStructure_of_gluing
    (hglue : SchemeAnalytificationGluingStatement.{u}) :
    SchemeAnalytificationAnalyticStructureStatement.{u} := by
  intro K _ _ _ X f _
  obtain ⟨-, h2, h3, -, -⟩ := hglue K X f
  exact analyticStructure_of_openGluing ⟨h2, h3⟩

end Langlands.Analytic.SchemeAnalytification
