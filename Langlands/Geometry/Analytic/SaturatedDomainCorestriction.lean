import Langlands.Geometry.Analytic.SaturatedSourceCategory
import Langlands.Geometry.Analytic.OriginalDomainStrongRestriction

/-! # Actual domain atlases and source refinements for codomain restriction -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set Filter Topology PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}

/-- The actual subspace atlas retains closure under every full local domain. -/
theorem subspaceAtlas_hasAllLocalDomains (ha : a.HasAllLocalDomains)
    (S : Set X) (hS : a.IsOriginalChartDomain S) :
    (a.subspaceAtlas S hS).HasAllLocalDomains := by
  ext T
  constructor
  · rintro ⟨U, rfl⟩
    let V : LocalDomain a := ⟨U.index.val, U.domain⟩
    obtain ⟨i, hi⟩ := ha.exists_chart V
    have hiS : Set.range (a.chart i) ⊆ S := by
      rw [hi]
      exact (Set.image_subset_range _ _).trans U.index.property
    refine ⟨⟨i, hiS⟩, ?_⟩
    change Set.range (a.subspaceChart S ⟨i, hiS⟩) = U.locus
    refine (a.range_subspaceChart S ⟨i, hiS⟩).trans ?_
    ext x
    constructor
    · intro hx
      rw [hi] at hx
      obtain ⟨y, hy, hyx⟩ := hx
      exact ⟨y, hy, Subtype.ext hyx⟩
    · rintro ⟨y, hy, hyx⟩
      rw [hi]
      exact ⟨y, hy, congrArg Subtype.val hyx⟩
  · rintro ⟨i, rfl⟩
    exact ⟨⟨i, Domain.whole K (a.algebra i.val)⟩, Set.image_univ⟩

end IndexedAffinoidAtlas

namespace SaturatedAtlasPresentation

variable {A B C : SaturatedAtlasPresentation.{u, v, w} K}

/-- The original domain subspace with its proved full local-domain closure. -/
def originalDomain (B : SaturatedAtlasPresentation.{u, v, w} K)
    (S : B.presentation.atlas.OriginalChartDomain) :
    SaturatedAtlasPresentation.{u, v, w} K where
  presentation := B.presentation.originalDomainPresentation S
  hasAllLocalDomains := subspaceAtlas_hasAllLocalDomains B.hasAllLocalDomains S.carrier S.is_domain

/-- The full inclusion retains every admissible original bounded restriction. -/
def originalDomainInclusion (B : SaturatedAtlasPresentation.{u, v, w} K)
    (S : B.presentation.atlas.OriginalChartDomain) : B.originalDomain S ⟶ B :=
  B.presentation.subspaceStrongInclusion S.carrier S.is_domain

@[simp]
theorem originalDomainInclusion_apply (S : B.presentation.atlas.OriginalChartDomain)
    (x : S.carrier) : (B.originalDomainInclusion S).baseMap x = x.val := rfl

/-- The source charts whose images fit inside a target chart contained in S. -/
theorem sourceSelectionForDomain_locallyRefining (f : A ⟶ B)
    (S : B.presentation.atlas.OriginalChartDomain)
    (himage : ∀ x, f.baseMap x ∈ S) :
    A.presentation.atlas.IsLocallyRefiningSelection
      (f.sourceSelectionForTarget (fun j => Set.range (B.presentation.atlas.chart j) ⊆ S)) := by
  classical
  rintro _ ⟨i, rfl⟩ x hx
  obtain ⟨j, hj⟩ := f.target_exists i
  have hSj := S.is_domain.inter B.presentation.atlas
    (B.presentation.atlas.isOriginalChartDomain_chart j)
  obtain ⟨σ, hf, hs, hm, hn⟩ :=
    (AtlasTopology.isQuasinet_restrictedFamily_iff _ _).mp hSj
      _ (Set.mem_singleton _) (f.baseMap x) ⟨himage x, hj ⟨x, hx, rfl⟩⟩
  let T : Set A.presentation.space := Set.range (A.presentation.atlas.chart i)
  let δ : Set (Set A.presentation.space) := (fun V => T ∩ f.baseMap ⁻¹' V) '' σ
  have hδ : ⋃₀ δ = T ∩ f.baseMap ⁻¹' ⋃₀ σ := by
    ext y
    constructor
    · rintro ⟨_, ⟨V, hV, rfl⟩, hy⟩
      exact ⟨hy.1, V, hV, hy.2⟩
    · rintro ⟨hyT, V, hV, hyV⟩
      exact ⟨_, ⟨V, hV, rfl⟩, hyT, hyV⟩
  refine ⟨δ, hf.image _, ?_, ?_, ?_⟩
  · rintro _ ⟨V, hV, rfl⟩
    obtain ⟨k, hk⟩ := hs hV
    change Set.range (B.presentation.atlas.chart k) = V at hk
    have hkj : Set.range (B.presentation.atlas.chart k) ⊆
        Set.range (B.presentation.atlas.chart j) := by
      rw [hk]
      exact (hm V hV).1.trans Set.inter_subset_right
    have hkS : Set.range (B.presentation.atlas.chart k) ⊆ S := by
      rw [hk]
      exact (hm V hV).1.trans Set.inter_subset_left
    let U : LocalDomain A.presentation.atlas :=
      ⟨i, Domain.whole K (A.presentation.atlas.algebra i)⟩
    have hU : U.locus = T := Set.image_univ
    have hlocal : f.baseMap '' U.locus ⊆ Set.range (B.presentation.atlas.chart j) := hU ▸ hj
    refine ⟨⟨f.inverseImageOriginalChart A.hasAllLocalDomains U j hlocal k hkj,
      f.inverseImageOriginalChart_selected A.hasAllLocalDomains
        (fun j => Set.range (B.presentation.atlas.chart j) ⊆ S)
        U j hlocal k hkS hkj⟩, ?_⟩
    exact (f.range_inverseImageOriginalChart A.hasAllLocalDomains U j hlocal k hkj).trans
      (by rw [hU, hk])
  · rintro _ ⟨V, hV, rfl⟩
    exact ⟨Set.inter_subset_left, hx, (hm V hV).2⟩
  · rw [hδ]
    have hc : Tendsto f.baseMap (𝓝[T] x)
        (𝓝[S.carrier ∩ Set.range (B.presentation.atlas.chart j)] (f.baseMap x)) :=
      f.baseMap.continuous.continuousWithinAt.tendsto_nhdsWithin
        (fun y hy => ⟨himage y, hj ⟨y, hy, rfl⟩⟩)
    exact Filter.inter_mem self_mem_nhdsWithin (hc hn)

/-- A constructed downward-closed source refinement subordinate to S. -/
def domainSourceSelection (f : A ⟶ B)
    (S : B.presentation.atlas.OriginalChartDomain)
    (himage : ∀ x, f.baseMap x ∈ S) : A.presentation.atlas.RefiningSelection where
  carrier := f.sourceSelectionForTarget
    (fun j => Set.range (B.presentation.atlas.chart j) ⊆ S)
  downward_closed := by
    intro i i' hii' hi'
    obtain ⟨j, hj, hij⟩ := hi'
    exact ⟨j, hj, (Set.image_mono hii').trans hij⟩
  locally_refining := sourceSelectionForDomain_locallyRefining f S himage

/-- Corestrict the continuous numerator to the literal target subspace. -/
def domainBaseMap (f : A ⟶ B) (S : B.presentation.atlas.OriginalChartDomain)
    (himage : ∀ x, f.baseMap x ∈ S) : C(A.presentation.space, S.carrier) :=
  ⟨fun x => ⟨f.baseMap x, himage x⟩, f.baseMap.continuous.subtype_mk _⟩

theorem domainBaseMap_admissible_iff (f : A ⟶ B)
    (S : B.presentation.atlas.OriginalChartDomain) (himage : ∀ x, f.baseMap x ∈ S)
    (i : A.presentation.atlas.Index) (j : B.presentation.atlas.SubspaceChart S.carrier) :
    domainBaseMap f S himage '' Set.range (A.presentation.atlas.chart i) ⊆
        Set.range ((B.originalDomain S).presentation.atlas.chart j) ↔
      f.baseMap '' Set.range (A.presentation.atlas.chart i) ⊆
        Set.range (B.presentation.atlas.chart j.val) := by
  constructor <;> intro h <;> rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  · obtain ⟨y, hy⟩ := h ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨y, congrArg Subtype.val hy⟩
  · obtain ⟨y, hy⟩ := h ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨y, Subtype.ext hy⟩

/-- The source refinement supplies the missing target-chart witnesses.
Every admissible bounded pullback is retained literally from f. -/
def domainFactor (f : A ⟶ B) (S : B.presentation.atlas.OriginalChartDomain)
    (himage : ∀ x, f.baseMap x ∈ S) :
    A.refiningSubpresentation (domainSourceSelection f S himage) ⟶ B.originalDomain S where
  baseMap := domainBaseMap f S himage
  target_exists i := by
    obtain ⟨j, hj, hij⟩ := i.property
    exact ⟨⟨j, hj⟩, (domainBaseMap_admissible_iff f S himage i.val ⟨j, hj⟩).mpr hij⟩
  pullback i j h := f.pullback i.val j.val
    ((domainBaseMap_admissible_iff f S himage i.val j).mp h)
  chart_comm i j h x := Subtype.ext (f.chart_comm i.val j.val _ x)
  restriction_comm i i' j j' hi hj h h' :=
    f.restriction_comm i.val i'.val j.val j'.val hi
      (B.presentation.atlas.chart_subset_of_subspaceSubset S.carrier j j' hj)
      ((domainBaseMap_admissible_iff f S himage i.val j).mp h)
      ((domainBaseMap_admissible_iff f S himage i'.val j').mp h')

@[simp]
theorem domainFactor_apply (f : A ⟶ B) (S : B.presentation.atlas.OriginalChartDomain)
    (himage : ∀ x, f.baseMap x ∈ S) (x : A.presentation.space) :
    ((domainFactor f S himage).baseMap x).val = f.baseMap x := rfl

theorem domainFactor_pullback (f : A ⟶ B) (S : B.presentation.atlas.OriginalChartDomain)
    (himage : ∀ x, f.baseMap x ∈ S)
    (i : (A.refiningSubpresentation (domainSourceSelection f S himage)).presentation.atlas.Index)
    (j : (B.originalDomain S).presentation.atlas.Index)
    (h : (domainFactor f S himage).baseMap ''
      Set.range ((A.refiningSubpresentation (domainSourceSelection f S himage)).presentation.atlas.chart i) ⊆
        Set.range ((B.originalDomain S).presentation.atlas.chart j)) :
    (domainFactor f S himage).pullback i j h =
      f.pullback i.val j.val ((domainBaseMap_admissible_iff f S himage i.val j).mp h) := rfl

/-- Composition with the inclusion recovers the whole bounded pullback,
not just its induced map on spectrum points. -/
theorem originalDomainInclusion_comp_pullback
    (S : B.presentation.atlas.OriginalChartDomain) (f : A ⟶ B.originalDomain S)
    (i : A.presentation.atlas.Index)
    (j : (B.originalDomain S).presentation.atlas.Index)
    (hf : f.baseMap '' Set.range (A.presentation.atlas.chart i) ⊆
      Set.range ((B.originalDomain S).presentation.atlas.chart j))
    (h : (f ≫ B.originalDomainInclusion S).baseMap ''
      Set.range (A.presentation.atlas.chart i) ⊆
        Set.range (B.presentation.atlas.chart j.val)) :
    (f ≫ B.originalDomainInclusion S).pullback i j.val h = f.pullback i j hf := by
  have hinc : (B.originalDomainInclusion S).baseMap ''
      Set.range ((B.originalDomain S).presentation.atlas.chart j) ⊆
        Set.range (B.presentation.atlas.chart j.val) := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    exact ⟨x, rfl⟩
  refine (AffinoidAtlasPresentation.StrongHom.saturatedComp_pullback
    f (B.originalDomainInclusion S) A.hasAllLocalDomains
    (B.originalDomain S).hasAllLocalDomains i j j.val hf hinc h).trans ?_
  change (f.pullback i j hf).comp (B.presentation.atlas.restriction j.val j.val _) = _
  rw [B.presentation.atlas.restriction_id]
  exact BoundedAlgHom.comp_id _

/-- The constructed factor commutes with the actual same-space source
refinement as equality of complete strong morphisms. -/
theorem domainFactor_comp_inclusion (f : A ⟶ B)
    (S : B.presentation.atlas.OriginalChartDomain) (himage : ∀ x, f.baseMap x ∈ S) :
    domainFactor f S himage ≫ B.originalDomainInclusion S =
      A.refiningSubatlasInclusion (domainSourceSelection f S himage) ≫ f := by
  let P := domainSourceSelection f S himage
  refine AffinoidAtlasPresentation.StrongHom.ext_of_saturated
    (f := domainFactor f S himage ≫ B.originalDomainInclusion S)
    (g := A.refiningSubatlasInclusion P ≫ f)
    (A.refiningSubpresentation P).hasAllLocalDomains rfl ?_
  intro i
  obtain ⟨j, hj, hij⟩ := i.property
  have hfactor : (domainFactor f S himage).baseMap ''
      Set.range ((A.refiningSubpresentation P).presentation.atlas.chart i) ⊆
        Set.range ((B.originalDomain S).presentation.atlas.chart ⟨j, hj⟩) :=
    (domainBaseMap_admissible_iff f S himage i.val ⟨j, hj⟩).mpr hij
  have hsource : (A.refiningSubatlasInclusion P).baseMap ''
      Set.range ((A.refiningSubpresentation P).presentation.atlas.chart i) ⊆
        Set.range (A.presentation.atlas.chart i.val) := by
    rintro _ ⟨x, hx, rfl⟩
    exact hx
  refine ⟨j, hij, ?_⟩
  rw [originalDomainInclusion_comp_pullback S (domainFactor f S himage)
    i ⟨j, hj⟩ hfactor hij]
  symm
  refine (AffinoidAtlasPresentation.StrongHom.saturatedComp_pullback
    (A.refiningSubatlasInclusion P) f
    (A.refiningSubpresentation P).hasAllLocalDomains A.hasAllLocalDomains
    i i.val j hsource hij hij).trans ?_
  change (A.presentation.atlas.restriction i.val i.val _).comp
    (f.pullback i.val j hij) = f.pullback i.val j hij
  rw [A.presentation.atlas.restriction_id, BoundedAlgHom.id_comp]

/-- A domain inclusion cancels complete strong maps, including all bounded
pullbacks invisible to their underlying point maps. -/
instance originalDomainInclusion_mono (S : B.presentation.atlas.OriginalChartDomain) :
    Mono (B.originalDomainInclusion S) where
  right_cancellation {Z} f g heq := by
    have hbase : f.baseMap = g.baseMap := by
      ext x
      apply Subtype.ext
      exact congrArg (fun F : Z ⟶ B => F.baseMap x) heq
    refine AffinoidAtlasPresentation.StrongHom.ext_of_saturated
      Z.hasAllLocalDomains hbase ?_
    intro i
    obtain ⟨j, hf⟩ := f.target_exists i
    have hg : g.baseMap '' Set.range (Z.presentation.atlas.chart i) ⊆
        Set.range ((B.originalDomain S).presentation.atlas.chart j) := by
      rw [← hbase]
      exact hf
    have hinc : (B.originalDomainInclusion S).baseMap ''
        Set.range ((B.originalDomain S).presentation.atlas.chart j) ⊆
          Set.range (B.presentation.atlas.chart j.val) := by
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨x, rfl⟩
    have hfc := f.comp_admissible (B.originalDomainInclusion S) i j j.val hf hinc
    have hgc := g.comp_admissible (B.originalDomainInclusion S) i j j.val hg hinc
    refine ⟨j, hf, ?_⟩
    have hp := AffinoidAtlasPresentation.StrongHom.pullback_congr heq i j.val hfc hgc
    rw [originalDomainInclusion_comp_pullback S f i j hf hfc,
      originalDomainInclusion_comp_pullback S g i j hg hgc] at hp
    exact hp

/-- Postcomposition by an original full strong map retains the same
source representative and composes its complete numerator. -/
theorem sourceHomComp_ι_strong (P : A.presentation.atlas.RefiningSelection)
    (f : A.refiningSubpresentation P ⟶ B) (g : B ⟶ C) :
    sourceHomComp (sourceHomι P f) (SourceCategory.strongFunctor.map g) =
      sourceHomι P (f ≫ g) := by
  apply sourceHomEquiv.injective
  erw [sourceHomEquiv_comp, sourceHomEquiv_ι, sourceHomEquiv_ι]
  change localizedRightFraction (sourceRefinementFraction P f) ≫
    sourceHomEquiv (sourceHomEquiv.symm (localizationFunctor.map g)) =
      localizedRightFraction (sourceRefinementFraction P (f ≫ g))
  rw [Equiv.apply_symm_apply]
  change ((localizedQuasiIso _ _).inv ≫ localizationFunctor.map f) ≫
    localizationFunctor.map g = (localizedQuasiIso _ _).inv ≫ localizationFunctor.map (f ≫ g)
  rw [Functor.map_comp, Category.assoc]
  rfl

namespace SourceCategory

/-- The actual original-chart domain inclusion in the source-quotient
analytic morphism category. -/
def domainInclusion (B : SaturatedAtlasPresentation.{u, v, w} K)
    (S : B.presentation.atlas.OriginalChartDomain) :
    ofPresentation (B.originalDomain S) ⟶ ofPresentation B :=
  strongFunctor.map (B.originalDomainInclusion S)

/-- Common-source equality and complete strong cancellation give monicity
after localization; faithfulness of the original functor is unnecessary. -/
instance domainInclusion_mono (S : B.presentation.atlas.OriginalChartDomain) :
    Mono (domainInclusion B S) where
  right_cancellation {Z} F G := by
    change SourceHomQuotient Z.toPresentation (B.originalDomain S) at F G
    refine Quotient.inductionOn₂ F G ?_
    rintro ⟨P, f⟩ ⟨Q, g⟩ heq
    change sourceHomComp (sourceHomι P f) (strongFunctor.map (B.originalDomainInclusion S)) =
      sourceHomComp (sourceHomι Q g) (strongFunctor.map (B.originalDomainInclusion S)) at heq
    erw [sourceHomComp_ι_strong, sourceHomComp_ι_strong, sourceHomι_eq_iff] at heq
    obtain ⟨R, hRP, hRQ, heq⟩ := heq
    apply (sourceHomι_eq_iff f g).2
    refine ⟨R, hRP, hRQ, ?_⟩
    apply (cancel_mono (B.originalDomainInclusion S)).1
    simpa only [refiningHomRestriction, Category.assoc] using heq

/-- A localized map whose literal continuous image lies in the domain has
an actual factor. Both the extra source refinement and its full numerator
are constructed rather than assumed. -/
theorem exists_domainFactor (S : B.presentation.atlas.OriginalChartDomain)
    (F : ofPresentation A ⟶ ofPresentation B)
    (himage : ∀ x, spaceFunctor.map F x ∈ S) :
    ∃ G : ofPresentation A ⟶ ofPresentation (B.originalDomain S),
      G ≫ domainInclusion B S = F := by
  revert himage
  refine Quotient.inductionOn F ?_
  rintro ⟨P, f⟩ himage
  change ∀ x, spaceFunctor.map (sourceHomι P f) x ∈ S at himage
  erw [spaceFunctor_map_ι] at himage
  have hf : ∀ x, f.baseMap x ∈ S := himage
  let Q := domainSourceSelection f S hf
  let φ : (quasiIsomorphisms (K := K)).RightFraction A (B.originalDomain S) :=
    ⟨(A.refiningSubpresentation P).refiningSubatlasInclusion Q ≫
        A.refiningSubatlasInclusion P,
      (quasiIsomorphisms (K := K)).comp_mem _ _
        (isQuasiIso_refiningSubatlasInclusion Q) (isQuasiIso_refiningSubatlasInclusion P),
      domainFactor f S hf⟩
  refine ⟨sourceHomOfFraction φ, ?_⟩
  apply sourceHomEquiv.injective
  change sourceHomEquiv (sourceHomComp (sourceHomOfFraction φ)
    (strongFunctor.map (B.originalDomainInclusion S))) = sourceHomEquiv (sourceHomι P f)
  erw [sourceHomEquiv_comp, sourceHomEquiv_ofFraction, sourceHomEquiv_ι]
  change localizedRightFraction φ ≫
    sourceHomEquiv (sourceHomEquiv.symm (localizationFunctor.map (B.originalDomainInclusion S))) =
      localizedRightFraction (sourceRefinementFraction P f)
  rw [Equiv.apply_symm_apply]
  have : IsIso (localizationFunctor.map φ.s) :=
    Localization.inverts localizationFunctor (quasiIsomorphisms (K := K)) φ.s φ.hs
  apply (cancel_epi (localizationFunctor.map φ.s)).1
  rw [← Category.assoc, localizationFunctor_map_s_comp_localizedRightFraction,
    ← Functor.map_comp]
  change localizationFunctor.map (domainFactor f S hf ≫ B.originalDomainInclusion S) =
    localizationFunctor.map
      ((A.refiningSubpresentation P).refiningSubatlasInclusion Q ≫
        A.refiningSubatlasInclusion P) ≫
      localizedRightFraction (sourceRefinementFraction P f)
  erw [domainFactor_comp_inclusion, Functor.map_comp, Functor.map_comp, Category.assoc,
    localizationFunctor_map_s_comp_localizedRightFraction, ← Functor.map_comp]

/-- The actual domain object has the image-only unique factorization
property for all arrows of the source-quotient category. -/
theorem existsUnique_domainFactor (S : B.presentation.atlas.OriginalChartDomain)
    (F : ofPresentation A ⟶ ofPresentation B)
    (himage : ∀ x, spaceFunctor.map F x ∈ S) :
    ∃! G : ofPresentation A ⟶ ofPresentation (B.originalDomain S),
      G ≫ domainInclusion B S = F := by
  obtain ⟨G, hG⟩ := exists_domainFactor S F himage
  exact ⟨G, hG, fun H hH => (cancel_mono (domainInclusion B S)).1 (hH.trans hG.symm)⟩

/-- Choose the proved unique factor in the actual quotient category. -/
def domainLift (S : B.presentation.atlas.OriginalChartDomain)
    (F : ofPresentation A ⟶ ofPresentation B)
    (himage : ∀ x, spaceFunctor.map F x ∈ S) :
    ofPresentation A ⟶ ofPresentation (B.originalDomain S) :=
  Classical.choose (exists_domainFactor S F himage)

@[simp]
theorem domainLift_comp_inclusion (S : B.presentation.atlas.OriginalChartDomain)
    (F : ofPresentation A ⟶ ofPresentation B)
    (himage : ∀ x, spaceFunctor.map F x ∈ S) :
    domainLift S F himage ≫ domainInclusion B S = F :=
  Classical.choose_spec (exists_domainFactor S F himage)

@[simp]
theorem domainInclusion_apply (S : B.presentation.atlas.OriginalChartDomain)
    (x : S.carrier) : spaceFunctor.map (domainInclusion B S) x = x.val := by
  change spaceFunctor.map (strongFunctor.map (B.originalDomainInclusion S)) x = _
  rw [spaceFunctor_map_strong]
  rfl

/-- The chosen quotient factor has exactly the original continuous map,
with its codomain restricted to the literal domain subspace. -/
@[simp]
theorem domainLift_apply (S : B.presentation.atlas.OriginalChartDomain)
    (F : ofPresentation A ⟶ ofPresentation B)
    (himage : ∀ x, spaceFunctor.map F x ∈ S) (x : A.presentation.space) :
    (spaceFunctor.map (domainLift S F himage) x).val = spaceFunctor.map F x := by
  have h := congrArg (fun H : ofPresentation A ⟶ ofPresentation B => spaceFunctor.map H x)
    (domainLift_comp_inclusion S F himage)
  rw [Functor.map_comp] at h
  exact (domainInclusion_apply S (spaceFunctor.map (domainLift S F himage) x)).symm.trans h

/-- Every arrow into the constructed domain has ambient image in that domain. -/
theorem domainInclusion_comp_image (S : B.presentation.atlas.OriginalChartDomain)
    (G : ofPresentation A ⟶ ofPresentation (B.originalDomain S)) :
    ∀ x, spaceFunctor.map (G ≫ domainInclusion B S) x ∈ S := by
  intro x
  rw [Functor.map_comp]
  change spaceFunctor.map (domainInclusion B S) (spaceFunctor.map G x) ∈ S
  erw [domainInclusion_apply]
  exact (spaceFunctor.map G x).property

/-- Postcomposition with the actual inclusion identifies domain-valued
morphisms with precisely the ambient morphisms whose point image lies in S. -/
def domainHomEquiv (A B : SaturatedAtlasPresentation.{u, v, w} K)
    (S : B.presentation.atlas.OriginalChartDomain) :
    (ofPresentation A ⟶ ofPresentation (B.originalDomain S)) ≃
      {F : ofPresentation A ⟶ ofPresentation B // ∀ x, spaceFunctor.map F x ∈ S} where
  toFun G := ⟨G ≫ domainInclusion B S, domainInclusion_comp_image S G⟩
  invFun F := domainLift S F.val F.property
  left_inv G := by
    apply (cancel_mono (domainInclusion B S)).1
    exact domainLift_comp_inclusion S (G ≫ domainInclusion B S)
      (domainInclusion_comp_image S G)
  right_inv F := Subtype.ext (domainLift_comp_inclusion S F.val F.property)

end SourceCategory

end SaturatedAtlasPresentation
end Langlands.Analytic
