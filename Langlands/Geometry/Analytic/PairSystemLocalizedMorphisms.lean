import Langlands.Geometry.Analytic.FullRecognitionPairLocalCondition
import Langlands.Geometry.Analytic.SaturatedStrongLocalization

/-! # Morphisms of the localized category from pair systems with the local condition -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation.AdmissiblePairSystem

variable {A B : AffinoidAtlasPresentation.{u, v, w} K} (p : AdmissiblePairSystem A B)

/-- Source charts mapped by the pair system into some target chart. -/
def AdmissibleSource (i : A.atlas.Index) : Prop :=
  ∃ j : B.atlas.Index, p.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)

/-- Admissibility passes to every smaller source chart. -/
theorem admissibleSource_of_subset {i i' : A.atlas.Index}
    (h : Set.range (A.atlas.chart i) ⊆ Set.range (A.atlas.chart i'))
    (hi' : p.AdmissibleSource i') : p.AdmissibleSource i := by
  obtain ⟨j, hj⟩ := hi'
  exact ⟨j, (Set.image_mono h).trans hj⟩

/-- Berkovich's argument: the local condition makes the admissible source
charts a quasinet, and downward closure inside the original net makes them a
net. -/
theorem isNetSelection_admissibleSource (hp : p.LocalCondition) :
    A.atlas.IsNetSelection p.AdmissibleSource := by
  refine ⟨fun x => ?_, ?_⟩
  · obtain ⟨I, hIf, hIx, hIimg, hIs, -⟩ := hp x
    refine ⟨(fun q : A.atlas.Index × B.atlas.Index => Set.range (A.atlas.chart q.1)) '' I,
      hIf.image _, ?_, ?_, ?_⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact ⟨⟨q.1, q.2, hIimg q hq⟩, rfl⟩
    · rintro _ ⟨q, hq, rfl⟩
      exact hIx q hq
    · rw [Set.sUnion_image]
      exact hIs
  · rintro U ⟨i, rfl⟩ V ⟨k, rfl⟩
    have hnet := A.atlas.isNet_chartFamily.2 _ ⟨i.val, rfl⟩ _ ⟨k.val, rfl⟩
    refine hnet.mono ?_
    rintro W ⟨V', ⟨l, rfl⟩, hV', rfl⟩
    exact ⟨Set.range (A.atlas.chart l),
      ⟨⟨l, p.admissibleSource_of_subset (hV'.trans Set.inter_subset_left) i.property⟩, rfl⟩,
      hV', rfl⟩

/-- The pair system restricted to its admissible source net is a strong map. -/
def admissibleNetStrongHom (hp : p.LocalCondition) :
    StrongHom (A.netSubpresentation p.AdmissibleSource (p.isNetSelection_admissibleSource hp))
      B where
  baseMap := p.baseMap
  target_exists i := i.property
  pullback i j h := p.pullback i.val j h
  chart_comm i j h x := p.chart_comm i.val j h x
  restriction_comm i i' j j' hi hj h h' := p.restriction_comm i.val i'.val j j' hi hj h h'

@[simp]
theorem admissibleNetStrongHom_baseMap (hp : p.LocalCondition) :
    (p.admissibleNetStrongHom hp).baseMap = p.baseMap := rfl

@[simp]
theorem admissibleNetStrongHom_pullback (hp : p.LocalCondition)
    (i : (A.netSubpresentation p.AdmissibleSource
      (p.isNetSelection_admissibleSource hp)).atlas.Index)
    (j : B.atlas.Index)
    (h : p.baseMap '' Set.range (A.atlas.chart i.val) ⊆ Set.range (B.atlas.chart j)) :
    (p.admissibleNetStrongHom hp).pullback i j h = p.pullback i.val j h := rfl

/-- If the source atlas contains all local domains, so does the admissible
net subatlas: a local domain of an admissible chart is the range of a source
chart, which is admissible by downward closure. -/
theorem hasAllLocalDomains_admissibleNet (hp : p.LocalCondition)
    (hA : A.atlas.HasAllLocalDomains) :
    (A.netSubpresentation p.AdmissibleSource
      (p.isNetSelection_admissibleSource hp)).atlas.HasAllLocalDomains := by
  refine Set.Subset.antisymm ?_
    (A.netSubpresentation p.AdmissibleSource
      (p.isNetSelection_admissibleSource hp)).atlas.chartFamily_subset_localDomainFamily
  rintro _ ⟨U, rfl⟩
  let U0 : LocalDomain A.atlas := ⟨U.index.val, U.domain⟩
  obtain ⟨k, hk⟩ := hA.exists_chart U0
  have hsub : Set.range (A.atlas.chart k) ⊆ Set.range (A.atlas.chart U.index.val) := by
    rw [hk]
    rintro _ ⟨x, _, rfl⟩
    exact Set.mem_range_self _
  exact ⟨⟨k, p.admissibleSource_of_subset hsub U.index.property⟩, hk⟩

end AffinoidAtlasPresentation.AdmissiblePairSystem

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Corestriction of a strong map to a net selection of target charts that
contains an admissible target for every source chart. Every bounded pullback
into a selected chart is retained. -/
def corestrictNetSubatlasTarget (f : StrongHom A B) (P : B.atlas.Index → Prop)
    (hP : B.atlas.IsNetSelection P)
    (ht : ∀ i, ∃ j, P j ∧
      f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j)) :
    StrongHom A (B.netSubpresentation P hP) where
  baseMap := f.baseMap
  target_exists i := by
    obtain ⟨j, hj, h⟩ := ht i
    exact ⟨⟨j, hj⟩, h⟩
  pullback i j h := f.pullback i j.val h
  chart_comm i j h x := f.chart_comm i j.val h x
  restriction_comm i i' j j' hi hj h h' := f.restriction_comm i i' j.val j'.val hi hj h h'

/-- Composing the corestriction with the identity-space inclusion of the
selected net recovers the original strong map. -/
theorem corestrictNetSubatlasTarget_saturatedComp (f : StrongHom A B)
    (P : B.atlas.Index → Prop) (hP : B.atlas.IsNetSelection P)
    (ht : ∀ i, ∃ j, P j ∧
      f.baseMap '' Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j))
    (hA : A.atlas.HasAllLocalDomains)
    (hB : (B.netSubpresentation P hP).atlas.HasAllLocalDomains) :
    (f.corestrictNetSubatlasTarget P hP ht).saturatedComp
      (B.strongNetSubatlasInclusion P hP) hA hB = f := by
  refine ext_of_saturated hA rfl fun i => ?_
  obtain ⟨j, hj, h⟩ := ht i
  have hinc : (B.strongNetSubatlasInclusion P hP).baseMap ''
      Set.range ((B.netSubpresentation P hP).atlas.chart ⟨j, hj⟩) ⊆
        Set.range (B.atlas.chart j) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  have hc : ((f.corestrictNetSubatlasTarget P hP ht).saturatedComp
      (B.strongNetSubatlasInclusion P hP) hA hB).baseMap ''
        Set.range (A.atlas.chart i) ⊆ Set.range (B.atlas.chart j) := h
  refine ⟨j, hc, ?_⟩
  rw [saturatedComp_pullback _ _ hA hB i ⟨j, hj⟩ j h hinc hc]
  change (f.pullback i j h).comp (B.atlas.restriction j j _) = f.pullback i j _
  rw [B.atlas.restriction_id]
  rfl

end AffinoidAtlasPresentation.StrongHom

namespace SaturatedAtlasPresentation

variable {A B : SaturatedAtlasPresentation.{u, v, w} K}
  (p : AffinoidAtlasPresentation.AdmissiblePairSystem A.presentation B.presentation)
  (hp : p.LocalCondition)

/-- The admissible source net of a pair system on a saturated source, as an
object of the saturated strong category. -/
def admissibleNet : SaturatedAtlasPresentation.{u, v, w} K where
  presentation := A.presentation.netSubpresentation p.AdmissibleSource
    (p.isNetSelection_admissibleSource hp)
  hasAllLocalDomains := p.hasAllLocalDomains_admissibleNet hp A.hasAllLocalDomains

/-- The identity-space inclusion of the admissible net, a quasi-isomorphism. -/
def admissibleNetInclusion : admissibleNet p hp ⟶ A :=
  A.presentation.strongNetSubatlasInclusion p.AdmissibleSource
    (p.isNetSelection_admissibleSource hp)

theorem admissibleNetInclusion_isQuasiIso :
    (admissibleNetInclusion p hp).IsQuasiIso :=
  A.presentation.isQuasiIso_strongNetSubatlasInclusion p.AdmissibleSource
    (p.isNetSelection_admissibleSource hp)

/-- The restricted strong map from the admissible net to the target. -/
def admissibleNetMap : admissibleNet p hp ⟶ B :=
  p.admissibleNetStrongHom hp

/-- The morphism of the localized category determined by a pair system with
the local condition: the inverse of the admissible-net inclusion followed by
the restricted strong map. -/
def pairSystemLocalizedHom :
    localizationFunctor.obj A ⟶ localizationFunctor.obj B :=
  (localizedQuasiIso (admissibleNetInclusion p hp) (admissibleNetInclusion_isQuasiIso p hp)).inv ≫
    localizationFunctor.map (admissibleNetMap p hp)

/-- Precomposed with the localized inclusion, the constructed morphism is the
localized restricted strong map. -/
theorem localizationFunctor_map_admissibleNetInclusion_comp :
    localizationFunctor.map (admissibleNetInclusion p hp) ≫ pairSystemLocalizedHom p hp =
      localizationFunctor.map (admissibleNetMap p hp) := by
  rw [pairSystemLocalizedHom, ← Category.assoc, localizedQuasiIso_hom_inv_id, Category.id_comp]

/-- The ambient continuous map of the constructed morphism is the pair
system's continuous map. -/
theorem localizedSpaceFunctor_map_pairSystemLocalizedHom :
    localizedSpaceFunctor.map (pairSystemLocalizedHom p hp) =
      TopCat.ofHom p.baseMap := by
  have h := congrArg (fun φ => localizedSpaceFunctor.map φ)
    (localizationFunctor_map_admissibleNetInclusion_comp p hp)
  simp only [Functor.map_comp, localizedSpaceFunctor_map] at h
  have hinc : TopCat.ofHom (admissibleNetInclusion p hp).baseMap = 𝟙 _ := rfl
  rw [hinc] at h
  erw [Category.id_comp] at h
  exact h

end SaturatedAtlasPresentation

namespace AffinoidAtlasPresentation.StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}
  (g : StrongHom A.saturatedPresentation B.saturatedPresentation)

/-- A strong map of local-domain enlargements determines, through its
full-recognition pair system and the local condition, a morphism of the
localized category between the two full recognitions. -/
def fullRecognitionLocalizedHom :
    SaturatedAtlasPresentation.localizationFunctor.obj
        (SaturatedAtlasPresentation.ofFullRecognition A) ⟶
      SaturatedAtlasPresentation.localizationFunctor.obj
        (SaturatedAtlasPresentation.ofFullRecognition B) :=
  SaturatedAtlasPresentation.pairSystemLocalizedHom
    (A := SaturatedAtlasPresentation.ofFullRecognition A)
    (B := SaturatedAtlasPresentation.ofFullRecognition B)
    g.fullRecognitionPairs g.fullRecognitionPairs_localCondition

/-- Every original local domain, viewed as a recognized subset, is an
admissible source of the full-recognition pair system. -/
theorem fullRecognitionPairs_admissibleSource_original (S : A.atlas.saturatedAtlas.Index) :
    g.fullRecognitionPairs.AdmissibleSource
      (A.atlas.saturatedAtlas.originalRecognitionIndex S) := by
  obtain ⟨T, hT⟩ := g.target_exists S
  refine ⟨B.atlas.saturatedAtlas.originalRecognitionIndex T, ?_⟩
  exact ((Set.image_mono
    (A.atlas.saturatedAtlas.recognitionAtlas_original_range S).subset).trans hT).trans
      (B.atlas.saturatedAtlas.recognitionAtlas_original_range T).superset

theorem localDomainToFullRecognition_admissibleTargets (S : A.atlas.saturatedAtlas.Index) :
    ∃ V, g.fullRecognitionPairs.AdmissibleSource V ∧
      A.localDomainToFullRecognition.baseMap '' Set.range (A.atlas.saturatedAtlas.chart S) ⊆
        Set.range (A.fullRecognitionPresentation.atlas.chart V) := by
  refine ⟨A.atlas.saturatedAtlas.originalRecognitionIndex S,
    g.fullRecognitionPairs_admissibleSource_original S, ?_⟩
  change _root_.id '' Set.range (A.atlas.saturatedAtlas.chart S) ⊆
    Set.range (A.atlas.saturatedAtlas.recognitionAtlas.chart
      (A.atlas.saturatedAtlas.originalRecognitionIndex S))
  rw [Set.image_id, A.atlas.saturatedAtlas.recognitionAtlas_original_range]

/-- The canonical map of the local-domain enlargement into full recognition,
corestricted to the admissible source net of the pair system. -/
def localDomainToAdmissibleNet :
    StrongHom A.saturatedPresentation
      (A.fullRecognitionPresentation.netSubpresentation g.fullRecognitionPairs.AdmissibleSource
        (g.fullRecognitionPairs.isNetSelection_admissibleSource
          g.fullRecognitionPairs_localCondition)) :=
  A.localDomainToFullRecognition.corestrictNetSubatlasTarget _ _
    g.localDomainToFullRecognition_admissibleTargets

theorem localDomainToAdmissibleNet_saturatedComp_baseMap :
    (g.localDomainToAdmissibleNet.saturatedComp
        (g.fullRecognitionPairs.admissibleNetStrongHom g.fullRecognitionPairs_localCondition)
        A.atlas.saturatedAtlas_hasAllLocalDomains
        (g.fullRecognitionPairs.hasAllLocalDomains_admissibleNet
          g.fullRecognitionPairs_localCondition
          A.fullRecognitionPresentation_hasAllLocalDomains)).baseMap =
      g.toFullRecognitionTarget.baseMap := rfl

/-- Followed by the restricted pair system, the corestricted canonical map is
the composite of `g` with the canonical map into the target full recognition. -/
theorem localDomainToAdmissibleNet_saturatedComp_admissibleNetStrongHom :
    g.localDomainToAdmissibleNet.saturatedComp
        (g.fullRecognitionPairs.admissibleNetStrongHom g.fullRecognitionPairs_localCondition)
        A.atlas.saturatedAtlas_hasAllLocalDomains
        (g.fullRecognitionPairs.hasAllLocalDomains_admissibleNet
          g.fullRecognitionPairs_localCondition
          A.fullRecognitionPresentation_hasAllLocalDomains) =
      g.toFullRecognitionTarget := by
  refine ext_of_saturated A.atlas.saturatedAtlas_hasAllLocalDomains
    g.localDomainToAdmissibleNet_saturatedComp_baseMap fun S => ?_
  obtain ⟨T, hT⟩ := g.target_exists S
  let V : A.atlas.saturatedAtlas.RecognizedSubset := A.atlas.saturatedAtlas.originalRecognitionIndex S
  let W : B.atlas.saturatedAtlas.RecognizedSubset := B.atlas.saturatedAtlas.originalRecognitionIndex T
  have hSV : Set.range (A.atlas.saturatedAtlas.chart S) ⊆ V.locus := by
    rw [← V.range_chart]
    exact (A.atlas.saturatedAtlas.recognitionAtlas_original_range S).symm.subset
  have hVW : g.baseMap '' Set.range V.chart ⊆ Set.range W.chart :=
    ((Set.image_mono
      (A.atlas.saturatedAtlas.recognitionAtlas_original_range S).subset).trans hT).trans
        (B.atlas.saturatedAtlas.recognitionAtlas_original_range T).superset
  have hSW : g.toFullRecognitionTarget.baseMap '' Set.range (A.atlas.saturatedAtlas.chart S) ⊆
      Set.range (B.fullRecognitionPresentation.atlas.chart W) :=
    (Set.image_mono (hSV.trans V.range_chart.superset)).trans hVW
  let Vs : {i : A.fullRecognitionPresentation.atlas.Index //
      g.fullRecognitionPairs.AdmissibleSource i} :=
    ⟨V, g.fullRecognitionPairs_admissibleSource_original S⟩
  refine ⟨W, hSW, ?_⟩
  have h1 : g.localDomainToAdmissibleNet.baseMap '' Set.range (A.atlas.saturatedAtlas.chart S) ⊆
      Set.range ((A.fullRecognitionPresentation.netSubpresentation
        g.fullRecognitionPairs.AdmissibleSource
          (g.fullRecognitionPairs.isNetSelection_admissibleSource
            g.fullRecognitionPairs_localCondition)).atlas.chart Vs) := by
    change _root_.id '' Set.range (A.atlas.saturatedAtlas.chart S) ⊆ Set.range V.chart
    rw [Set.image_id, V.range_chart]
    exact hSV
  have hVW' : (g.fullRecognitionPairs.admissibleNetStrongHom
      g.fullRecognitionPairs_localCondition).baseMap ''
        Set.range ((A.fullRecognitionPresentation.netSubpresentation
          g.fullRecognitionPairs.AdmissibleSource
            (g.fullRecognitionPairs.isNetSelection_admissibleSource
              g.fullRecognitionPairs_localCondition)).atlas.chart Vs) ⊆
        Set.range (B.fullRecognitionPresentation.atlas.chart W) := hVW
  refine (saturatedComp_pullback g.localDomainToAdmissibleNet
    (g.fullRecognitionPairs.admissibleNetStrongHom g.fullRecognitionPairs_localCondition)
    A.atlas.saturatedAtlas_hasAllLocalDomains
    (g.fullRecognitionPairs.hasAllLocalDomains_admissibleNet
      g.fullRecognitionPairs_localCondition
      A.fullRecognitionPresentation_hasAllLocalDomains) S Vs W h1 hVW' hSW).trans ?_
  exact g.toFullRecognitionTarget.originalRestriction_comp_recognizedSourceExtension
    V W hVW S hSV

/-- The canonical map of the local-domain enlargement into full recognition,
as a morphism of the saturated strong category. -/
def localDomainToFullRecognitionHom (A : AffinoidAtlasPresentation.{u, v, w} K) :
    SaturatedAtlasPresentation.ofSaturation A ⟶ SaturatedAtlasPresentation.ofFullRecognition A :=
  A.localDomainToFullRecognition

/-- The composite of `g` with the canonical map into the target full
recognition, as a morphism of the saturated strong category. -/
def toFullRecognitionTargetHom :
    SaturatedAtlasPresentation.ofSaturation A ⟶ SaturatedAtlasPresentation.ofFullRecognition B :=
  g.toFullRecognitionTarget

/-- The corestricted canonical map as a morphism of the saturated strong category. -/
def localDomainToAdmissibleNetHom :
    SaturatedAtlasPresentation.ofSaturation A ⟶
      SaturatedAtlasPresentation.admissibleNet
        (A := SaturatedAtlasPresentation.ofFullRecognition A)
        (B := SaturatedAtlasPresentation.ofFullRecognition B)
        g.fullRecognitionPairs g.fullRecognitionPairs_localCondition :=
  g.localDomainToAdmissibleNet

/-- The constructed localized morphism recovers `g`: after the localized
canonical map of the source enlargement into its full recognition, it is the
localized composite of `g` with the canonical map into the target full
recognition. -/
theorem localizationFunctor_map_comp_fullRecognitionLocalizedHom :
    SaturatedAtlasPresentation.localizationFunctor.map (localDomainToFullRecognitionHom A) ≫
      g.fullRecognitionLocalizedHom =
    SaturatedAtlasPresentation.localizationFunctor.map g.toFullRecognitionTargetHom := by
  have e1 : g.localDomainToAdmissibleNetHom ≫
      SaturatedAtlasPresentation.admissibleNetInclusion
        (A := SaturatedAtlasPresentation.ofFullRecognition A)
        (B := SaturatedAtlasPresentation.ofFullRecognition B)
        g.fullRecognitionPairs g.fullRecognitionPairs_localCondition =
      localDomainToFullRecognitionHom A :=
    A.localDomainToFullRecognition.corestrictNetSubatlasTarget_saturatedComp _ _
      g.localDomainToFullRecognition_admissibleTargets _ _
  have e2 : g.localDomainToAdmissibleNetHom ≫
      SaturatedAtlasPresentation.admissibleNetMap
        (A := SaturatedAtlasPresentation.ofFullRecognition A)
        (B := SaturatedAtlasPresentation.ofFullRecognition B)
        g.fullRecognitionPairs g.fullRecognitionPairs_localCondition =
      g.toFullRecognitionTargetHom :=
    g.localDomainToAdmissibleNet_saturatedComp_admissibleNetStrongHom
  rw [← e1, ← e2, Functor.map_comp, Functor.map_comp, Category.assoc]
  congr 1
  exact SaturatedAtlasPresentation.localizationFunctor_map_admissibleNetInclusion_comp
    (A := SaturatedAtlasPresentation.ofFullRecognition A)
    (B := SaturatedAtlasPresentation.ofFullRecognition B)
    g.fullRecognitionPairs g.fullRecognitionPairs_localCondition

end AffinoidAtlasPresentation.StrongHom

end Langlands.Analytic
