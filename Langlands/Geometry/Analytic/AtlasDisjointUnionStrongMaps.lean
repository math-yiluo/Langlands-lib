import Langlands.Geometry.Analytic.AtlasDisjointUnionMaps
import Langlands.Geometry.Analytic.CompatibleStrongQuasiIsomorphisms

/-! # Disjoint unions of presentations in the category of compatible strong maps -/

noncomputable section

universe u v w z

open Set Topology CategoryTheory CategoryTheory.Limits

namespace Langlands.Analytic.AtlasDisjointUnion

open AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {I : Type z} (A : I → AffinoidAtlasPresentation.{u, max z v, max z w} K)
  (hA : ∀ i, (A i).atlas.HasNonemptyCharts)

/-- The image of an original chart under the sigma injection is the corresponding chart of
the disjoint union. -/
theorem image_sigmaMk_range (i : I) (c : (A i).atlas.Index) :
    (fun x => (⟨i, x⟩ : (j : I) × (A j).space)) '' Set.range ((A i).atlas.chart c) =
      Set.range ((presentation A hA).atlas.chart ⟨i, c⟩) :=
  (range_chart (fun i => (A i).atlas) ⟨i, c⟩).symm

theorem range_subset_of_image_subset (i : I) (c : (A i).atlas.Index)
    {S : Set (presentation A hA).space}
    (h : (fun x => (⟨i, x⟩ : (j : I) × (A j).space)) ''
      Set.range ((A i).atlas.chart c) ⊆ S) :
    Set.range ((presentation A hA).atlas.chart ⟨i, c⟩) ⊆ S := by
  rwa [← image_sigmaMk_range A hA i c]

theorem sigmaMk_injective {i : I} {x y : (A i).space}
    (h : (⟨i, x⟩ : (j : I) × (A j).space) = ⟨i, y⟩) : x = y :=
  eq_of_heq (Sigma.mk.inj h).2

/-- Pullbacks of equal compatible strong maps agree. -/
theorem _root_.Langlands.Analytic.AffinoidAtlasPresentation.CompatibleStrongHom.pullback_congr
    {X Y : AffinoidAtlasPresentation.{u, v, w} K} {F F' : CompatibleStrongHom X Y}
    (h : F = F') (i : X.atlas.Index) (j : Y.atlas.Index)
    (hF : F.baseMap '' Set.range (X.atlas.chart i) ⊆ Set.range (Y.atlas.chart j))
    (hF' : F'.baseMap '' Set.range (X.atlas.chart i) ⊆ Set.range (Y.atlas.chart j)) :
    F.pullback i j hF = F'.pullback i j hF' := by
  subst h
  rfl

/-! ## The inclusion of a component -/

/-- The strong inclusion of a component into the disjoint union. Its pullbacks are the
restrictions of the disjoint-union atlas. -/
def inclusionStrong (i : I) : StrongHom (A i) (presentation A hA) where
  baseMap := ⟨fun x => (⟨i, x⟩ : (j : I) × (A j).space),
    continuous_sigmaMk (σ := fun j => (A j).space) (i := i)⟩
  target_exists c := ⟨⟨i, c⟩, (image_sigmaMk_range A hA i c).subset⟩
  pullback c d h := (presentation A hA).atlas.restriction ⟨i, c⟩ d
    (range_subset_of_image_subset A hA i c h)
  chart_comm c d h x := (presentation A hA).atlas.restriction_chart ⟨i, c⟩ d _ x
  restriction_comm c c' d d' hc hd h h' := by
    have hcc : Set.range ((presentation A hA).atlas.chart ⟨i, c⟩) ⊆
        Set.range ((presentation A hA).atlas.chart ⟨i, c'⟩) :=
      (chart_subset_iff (fun i => (A i).atlas) i c c').mpr hc
    have hcd := range_subset_of_image_subset A hA i c h
    have hc'd' := range_subset_of_image_subset A hA i c' h'
    exact ((presentation A hA).atlas.restriction_comp ⟨i, c⟩ ⟨i, c'⟩ d' hcc hc'd'
      (hcc.trans hc'd')).symm.trans
      ((presentation A hA).atlas.restriction_comp ⟨i, c⟩ d d' hcd hd (hcc.trans hc'd'))

@[simp]
theorem inclusionStrong_baseMap_apply (i : I) (x : (A i).space) :
    (inclusionStrong A hA i).baseMap x = (⟨i, x⟩ : Σ j, (A j).space) := rfl

/-- The compatible strong inclusion of a component. Compatibility is that of the identity
of the disjoint union. -/
def compatibleInclusion (i : I) : CompatibleStrongHom (A i) (presentation A hA) where
  toStrongHom := inclusionStrong A hA i
  compatible := StrongHom.hasLocallyCompatiblePullbacks_iff _ |>.mpr fun c j k hj hk =>
    StrongHom.hasCoherentPullbacks_id (presentation A hA) ⟨i, c⟩ j k
      (by simpa only [StrongHom.id, ContinuousMap.coe_id, Set.image_id] using
        range_subset_of_image_subset A hA i c hj)
      (by simpa only [StrongHom.id, ContinuousMap.coe_id, Set.image_id] using
        range_subset_of_image_subset A hA i c hk)

theorem inclusion_pullback_self (i : I) (c : (A i).atlas.Index)
    (h : (compatibleInclusion A hA i).baseMap '' Set.range ((A i).atlas.chart c) ⊆
      Set.range ((presentation A hA).atlas.chart ⟨i, c⟩)) :
    (compatibleInclusion A hA i).pullback c ⟨i, c⟩ h = BoundedAlgHom.id K ((A i).atlas.algebra c) :=
  (presentation A hA).atlas.restriction_id ⟨i, c⟩ subset_rfl

/-! ## Descent along the components -/

variable {A hA} {B : AffinoidAtlasPresentation.{u, max z v, max z w} K}
  (f : ∀ i, CompatibleStrongHom (A i) B)

/-- The continuous map on the disjoint union with the given components. -/
def descBaseMap : C((presentation A hA).space, B.space) :=
  ⟨fun x => (f x.1).baseMap x.2, continuous_sigma fun i => (f i).baseMap.continuous⟩

theorem image_descBaseMap (i : I) (c : (A i).atlas.Index) :
    descBaseMap (hA := hA) f '' Set.range ((presentation A hA).atlas.chart ⟨i, c⟩) =
      (f i).baseMap '' Set.range ((A i).atlas.chart c) := by
  ext y
  constructor
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨_, ⟨x, rfl⟩, rfl⟩

theorem image_descBaseMap' (c : (presentation A hA).atlas.Index) :
    descBaseMap (hA := hA) f '' Set.range ((presentation A hA).atlas.chart c) =
      (f c.1).baseMap '' Set.range ((A c.1).atlas.chart c.2) :=
  image_descBaseMap f c.1 c.2

/-- The strong map out of the disjoint union with the given components. -/
def descStrong : StrongHom (presentation A hA) B where
  baseMap := descBaseMap f
  target_exists c := by
    obtain ⟨j, hj⟩ := (f c.1).target_exists c.2
    exact ⟨j, (image_descBaseMap' f c).trans_subset hj⟩
  pullback c j h := (f c.1).pullback c.2 j ((image_descBaseMap' f c).symm.trans_subset h)
  chart_comm c j h x := (f c.1).chart_comm c.2 j _ x
  restriction_comm c c' j j' hc hj h h' := by
    rcases c with ⟨i, c⟩
    rcases c' with ⟨i', c'⟩
    obtain rfl : i = i' := tag_eq_of_subset (fun i => (A i).atlas) hA ⟨i, c⟩ ⟨i', c'⟩ hc
    exact (f i).restriction_comm c c' j j'
      ((chart_subset_iff (fun i => (A i).atlas) i c c').mp hc) hj _ _

/-- The compatible strong map out of the disjoint union with the given components. -/
def compatibleDesc : CompatibleStrongHom (presentation A hA) B where
  toStrongHom := descStrong f
  compatible c j k _ _ := (f c.1).compatible c.2 j k _ _

@[simp]
theorem desc_baseMap_apply (x : (presentation A hA).space) :
    (compatibleDesc (hA := hA) f).baseMap x = (f x.1).baseMap x.2 := rfl

theorem compatibleDesc_pullback (c : (presentation A hA).atlas.Index) (j : B.atlas.Index)
    (h : (compatibleDesc (hA := hA) f).baseMap '' Set.range ((presentation A hA).atlas.chart c) ⊆
      Set.range (B.atlas.chart j)) :
    (compatibleDesc f).pullback c j h =
      (f c.1).pullback c.2 j ((image_descBaseMap' f c).symm.trans_subset h) := rfl

/-- The descended map restricts to the given component maps. -/
theorem inclusion_comp_desc (i : I) : (compatibleInclusion A hA i).comp (compatibleDesc f) = f i := by
  refine CompatibleStrongHom.ext_of_pullback (ContinuousMap.ext fun _ => rfl) fun c => ?_
  obtain ⟨j, hj⟩ := (f i).target_exists c
  have h0 : ((compatibleInclusion A hA i).comp (compatibleDesc f)).baseMap '' Set.range ((A i).atlas.chart c) ⊆
      Set.range (B.atlas.chart j) := hj
  refine ⟨j, h0, ?_⟩
  have hf : (compatibleInclusion A hA i).baseMap '' Set.range ((A i).atlas.chart c) ⊆
      Set.range ((presentation A hA).atlas.chart ⟨i, c⟩) :=
    (image_sigmaMk_range A hA i c).subset
  have hg : (compatibleDesc (hA := hA) f).baseMap '' Set.range ((presentation A hA).atlas.chart ⟨i, c⟩) ⊆
      Set.range (B.atlas.chart j) :=
    (image_descBaseMap f i c).trans_subset hj
  rw [CompatibleStrongHom.comp_pullback (compatibleInclusion A hA i) (compatibleDesc f) c ⟨i, c⟩ j hf hg h0,
    inclusion_pullback_self]
  exact BoundedAlgHom.id_comp _

/-- Compatible strong maps out of the disjoint union are determined by their restrictions
to the components. -/
theorem compatibleHom_ext {g g' : CompatibleStrongHom (presentation A hA) B}
    (h : ∀ i, (compatibleInclusion A hA i).comp g = (compatibleInclusion A hA i).comp g') : g = g' := by
  have hb : g.baseMap = g'.baseMap := by
    ext ⟨i, x⟩
    exact congrArg (fun F : CompatibleStrongHom (A i) B => F.baseMap x) (h i)
  refine CompatibleStrongHom.ext_of_pullback hb fun c => ?_
  rcases c with ⟨i, c⟩
  obtain ⟨j, hj⟩ := g.target_exists ⟨i, c⟩
  refine ⟨j, hj, ?_⟩
  have hf : (compatibleInclusion A hA i).baseMap '' Set.range ((A i).atlas.chart c) ⊆
      Set.range ((presentation A hA).atlas.chart ⟨i, c⟩) :=
    (image_sigmaMk_range A hA i c).subset
  have hj' : g'.baseMap '' Set.range ((presentation A hA).atlas.chart ⟨i, c⟩) ⊆
      Set.range (B.atlas.chart j) := by
    rw [← hb]
    exact hj
  have h1 : ((compatibleInclusion A hA i).comp g).baseMap '' Set.range ((A i).atlas.chart c) ⊆
      Set.range (B.atlas.chart j) := by
    rw [CompatibleStrongHom.comp_baseMap, ContinuousMap.coe_comp, Set.image_comp]
    exact (Set.image_mono hf).trans hj
  have h2 : ((compatibleInclusion A hA i).comp g').baseMap '' Set.range ((A i).atlas.chart c) ⊆
      Set.range (B.atlas.chart j) := by
    rw [CompatibleStrongHom.comp_baseMap, ContinuousMap.coe_comp, Set.image_comp]
    exact (Set.image_mono hf).trans hj'
  have e := CompatibleStrongHom.pullback_congr (h i) c j h1 h2
  rw [CompatibleStrongHom.comp_pullback (compatibleInclusion A hA i) g c ⟨i, c⟩ j hf hj h1,
    CompatibleStrongHom.comp_pullback (compatibleInclusion A hA i) g' c ⟨i, c⟩ j hf hj' h2,
    inclusion_pullback_self] at e
  exact (BoundedAlgHom.id_comp _).symm.trans (e.trans (BoundedAlgHom.id_comp _))

/-! ## The coproduct in the compatible category -/

variable (A hA) in
/-- The disjoint union with its component inclusions, as a cofan in the category of
compatible strong maps. -/
def compatibleCofan : Cofan fun i => (⟨A i⟩ : CompatibleAtlasPresentation.{u, max z v, max z w} K) :=
  Cofan.mk ⟨presentation A hA⟩ fun i => compatibleInclusion A hA i

variable (A hA) in
/-- The disjoint union is a coproduct in the category of compatible strong maps. -/
def isColimitCofan : IsColimit (compatibleCofan A hA) :=
  Cofan.IsColimit.mk _ (fun s => compatibleDesc fun i => s.inj i)
    (fun s i => inclusion_comp_desc (fun i => s.inj i) i)
    (fun s _ hm => compatibleHom_ext fun i => (hm i).trans (inclusion_comp_desc (fun i => s.inj i) i).symm)

/-! ## Disjoint unions of quasi-isomorphisms -/

variable {A' : I → AffinoidAtlasPresentation.{u, max z v, max z w} K}
  (hA' : ∀ i, (A' i).atlas.HasNonemptyCharts) (s : ∀ i, CompatibleStrongHom (A' i) (A i))

variable (hA) in
/-- The componentwise map between disjoint unions. -/
def map : CompatibleStrongHom (presentation A' hA') (presentation A hA) :=
  compatibleDesc fun i => (s i).comp (compatibleInclusion A hA i)

@[simp]
theorem map_baseMap_apply (i : I) (x : (A' i).space) :
    (map hA hA' s).baseMap (⟨i, x⟩ : Σ j, (A' j).space) =
      (⟨i, (s i).baseMap x⟩ : Σ j, (A j).space) := rfl

theorem inclusion_comp_map (i : I) :
    (compatibleInclusion A' hA' i).comp (map hA hA' s) = (s i).comp (compatibleInclusion A hA i) :=
  inclusion_comp_desc _ i

/-- A disjoint union of quasi-isomorphisms is a quasi-isomorphism. -/
theorem isQuasiIso_map (hs : ∀ i, (s i).toStrongHom.IsQuasiIso) :
    (map hA hA' s).toStrongHom.IsQuasiIso := by
  refine ⟨?_, ?_⟩
  · exact IsHomeomorph.sigmaMap (X := fun i => (A' i).space) (Y := fun i => (A i).space)
      (f := id) (g := fun i => ((s i).baseMap : (A' i).space → (A i).space))
      Function.bijective_id fun i => (hs i).1
  · rintro ⟨i, c⟩ ⟨j, d⟩ h
    obtain ⟨x⟩ := hA' i c
    obtain ⟨y, hy⟩ := h ⟨_, ⟨x, rfl⟩, rfl⟩
    have hji : j = i := congrArg Sigma.fst hy
    subst i
    have hd : (s j).baseMap '' Set.range ((A' j).atlas.chart c) ⊆
        Set.range ((A j).atlas.chart d) := by
      rintro _ ⟨z, ⟨w, rfl⟩, rfl⟩
      obtain ⟨t, ht⟩ := h ⟨_, ⟨w, rfl⟩, rfl⟩
      exact ⟨t, sigmaMk_injective A (x := (A j).atlas.chart d t) ht⟩
    have hincl : (compatibleInclusion A hA j).baseMap '' Set.range ((A j).atlas.chart d) ⊆
        Set.range ((presentation A hA).atlas.chart ⟨j, d⟩) :=
      (image_sigmaMk_range A hA j d).subset
    have hcomp : ((s j).comp (compatibleInclusion A hA j)).baseMap '' Set.range ((A' j).atlas.chart c) ⊆
        Set.range ((presentation A hA).atlas.chart ⟨j, d⟩) :=
      (image_descBaseMap (fun i => (s i).comp (compatibleInclusion A hA i)) j c).symm.trans_subset h
    have hp : (map hA hA' s).pullback ⟨j, c⟩ ⟨j, d⟩ h = (s j).pullback c d hd := by
      change ((s j).comp (compatibleInclusion A hA j)).pullback c ⟨j, d⟩ hcomp = _
      rw [CompatibleStrongHom.comp_pullback (s j) (compatibleInclusion A hA j) c d ⟨j, d⟩ hd hincl hcomp,
        inclusion_pullback_self]
      exact BoundedAlgHom.comp_id _
    have hl : (map hA hA' s).chartImageLocus ⟨j, c⟩ ⟨j, d⟩ = (s j).chartImageLocus c d := by
      ext p
      constructor
      · rintro ⟨_, ⟨w, rfl⟩, hw⟩
        exact ⟨_, ⟨w, rfl⟩, sigmaMk_injective A (x := (s j).baseMap ((A' j).atlas.chart c w)) hw⟩
      · rintro ⟨_, ⟨w, rfl⟩, hw⟩
        exact ⟨_, ⟨w, rfl⟩, congrArg (Sigma.mk j) hw⟩
    rw [hp, hl]
    exact (hs j).2 c d hd

end Langlands.Analytic.AtlasDisjointUnion
