import Langlands.GroupScheme.IdentityJetAffineNeighborhood
import Langlands.GroupScheme.IdentityJetFunctorial
import Langlands.GroupScheme.RelativeIdentityComponent.BaseChange

/-! # Locality of fixed-rank smoothness along the unit -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.IdentityJet

variable {S T : Scheme.{u}} {G H : GroupScheme S}

section Smoothness

variable [LocallyOfFinitePresentation G.X.hom]

private theorem smoothAlongUnit_of_smooth_open {V : Scheme.{u}} (v : V ⟶ G.X.left)
    [IsOpenImmersion v] [Smooth (v ≫ G.X.hom)]
    (h : Set.range G.identitySection ⊆ Set.range v) : SmoothAlongUnit G := by
  intro s
  obtain ⟨x, hx⟩ := h ⟨s, rfl⟩
  rw [← Scheme.Hom.mem_smoothLocus, ← hx, ← Scheme.Hom.mem_preimage,
    Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.smoothLocus_eq_top]
  trivial

/-- A group smooth along the actual unit has an open smooth neighborhood of its unit. -/
theorem exists_smooth_unit_open (h : SmoothAlongUnit G) :
    ∃ V : G.X.left.Opens, Set.range G.identitySection ⊆ (V : Set G.X.left) ∧
      Smooth (V.ι ≫ G.X.hom) := by
  let V := G.X.hom.smoothLocus
  refine ⟨V, ?_, ?_⟩
  · rintro _ ⟨s, rfl⟩
    exact h s
  · apply Scheme.Hom.smoothLocus_eq_top_iff.mp
    rw [← Scheme.Hom.preimage_smoothLocus_eq]
    exact top_unique fun x _ => x.property

/-- Smoothness along the actual unit is preserved by every base change. -/
theorem SmoothAlongUnit.baseChange (h : SmoothAlongUnit G) (b : T ⟶ S) :
    SmoothAlongUnit ((GroupScheme.baseChange b).obj G) := by
  obtain ⟨V, hV, hsm⟩ := exists_smooth_unit_open h
  let K := (GroupScheme.baseChange b).obj G
  let W : Over S := Over.mk (V.ι ≫ G.X.hom)
  let i : W ⟶ G.X := Over.homMk V.ι rfl
  let i' : (Over.pullback b).obj W ⟶ K.X := (Over.pullback b).map i
  let p : K.X.left ⟶ G.X.left := pullback.fst G.X.hom b
  have hpb : IsPullback i'.left (pullback.fst W.hom b) p V.ι :=
    RelativeIdentityComponent.overPullback_isPullback b i
  have : LocallyOfFinitePresentation K.X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom b))
  have : IsOpenImmersion i'.left := MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    hpb.flip inferInstance
  have : Smooth W.hom := hsm
  have hW : Smooth ((Over.pullback b).obj W).hom :=
    inferInstanceAs (Smooth (pullback.snd W.hom b))
  have : Smooth (i'.left ≫ K.X.hom) := (Over.w i') ▸ hW
  apply smoothAlongUnit_of_smooth_open i'.left
  rintro _ ⟨t, rfl⟩
  rw [RelativeIdentityComponent.range_of_isPullback hpb]
  change p (K.identitySection t) ∈ Set.range V.ι
  have ht : p (K.identitySection t) = G.identitySection (b t) :=
    congrArg (fun f : T ⟶ G.X.left => f t) (identitySection_baseChange_fst b G)
  rw [ht, Scheme.Opens.range_ι]
  exact hV ⟨b t, rfl⟩

private theorem smoothLocus_comp_open {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (j : Y ⟶ Z) [LocallyOfFinitePresentation f] [IsOpenImmersion j] :
    (f ≫ j).smoothLocus = f.smoothLocus := by
  apply SetLike.ext
  intro x
  change ((f ≫ j).stalkMap x).hom.FormallySmooth ↔ (f.stalkMap x).hom.FormallySmooth
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp]
  exact RingHom.FormallySmooth.respectsIso.cancel_left_isIso (j.stalkMap (f x)) (f.stalkMap x)

/-- Smoothness along the unit descends from a base open cover. -/
theorem smoothAlongUnit_of_openCover (𝒰 : S.OpenCover)
    (h : ∀ i, SmoothAlongUnit ((GroupScheme.baseChange (𝒰.f i)).obj G)) : SmoothAlongUnit G := by
  intro s
  let b := 𝒰.f (𝒰.idx s)
  let K := (GroupScheme.baseChange b).obj G
  let p : K.X.left ⟶ G.X.left := pullback.fst G.X.hom b
  obtain ⟨t, ht⟩ := 𝒰.covers s
  have : IsOpenImmersion b := inferInstanceAs (IsOpenImmersion (𝒰.f (𝒰.idx s)))
  have : IsOpenImmersion p := inferInstanceAs (IsOpenImmersion (pullback.fst G.X.hom b))
  have : LocallyOfFinitePresentation K.X.hom :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.snd G.X.hom b))
  have he : p (K.identitySection t) = G.identitySection s :=
    (congrArg (fun f : 𝒰.X (𝒰.idx s) ⟶ G.X.left => f t)
      (identitySection_baseChange_fst b G)).trans (congrArg G.identitySection ht)
  have hw : p ≫ G.X.hom = K.X.hom ≫ b := pullback.condition
  rw [← Scheme.Hom.mem_smoothLocus, ← he, ← Scheme.Hom.mem_preimage,
    Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.mem_smoothLocus, hw,
    ← Scheme.Hom.mem_smoothLocus, smoothLocus_comp_open]
  exact h (𝒰.idx s) t

end Smoothness

section Rank

variable [IsSeparated G.X.hom] [LocallyOfFinitePresentation G.X.hom]

/-- The fixed-rank condition along the unit is preserved by arbitrary base change. -/
theorem SmoothAlongUnitOfRank.baseChange {r : ℕ} (h : SmoothAlongUnitOfRank G r) (b : T ⟶ S) :
    SmoothAlongUnitOfRank ((GroupScheme.baseChange b).obj G) r := by
  let K := (GroupScheme.baseChange b).obj G
  have hpb := baseChange_isPullback G b 1
  have : IsFinite (projection G 1) := finite_projection G 1
  have : Flat (projection G 1) := h.2.1
  refine ⟨h.1.baseChange b, MorphismProperty.of_isPullback (P := @Flat) hpb inferInstance, ?_⟩
  intro t
  change (projection K 1).finrank t = 1 + r
  rw [Scheme.Hom.finrank_of_isPullback _ _ _ _ hpb, h.2.2]

/-- The fixed-rank condition along the unit descends from a base open cover. -/
theorem smoothAlongUnitOfRank_of_openCover {r : ℕ} (𝒰 : S.OpenCover)
    (h : ∀ i, SmoothAlongUnitOfRank ((GroupScheme.baseChange (𝒰.f i)).obj G) r) :
    SmoothAlongUnitOfRank G r := by
  have : Flat (projection G 1) := by
    apply IsZariskiLocalAtTarget.of_openCover 𝒰
    intro i
    let k := baseChange_isPullback G (𝒰.f i) 1
    change Flat (pullback.snd (projection G 1) (𝒰.f i))
    apply (MorphismProperty.cancel_left_of_respectsIso @Flat k.isoPullback.hom _).mp
    rw [k.isoPullback_hom_snd]
    exact (h i).2.1
  have : IsFinite (projection G 1) := finite_projection G 1
  refine ⟨smoothAlongUnit_of_openCover 𝒰 (fun i => (h i).1), inferInstance, ?_⟩
  intro s
  obtain ⟨t, ht⟩ := 𝒰.covers s
  rw [← ht, ← Scheme.Hom.finrank_of_isPullback _ _ _ _ (baseChange_isPullback G (𝒰.f (𝒰.idx s)) 1) t]
  exact (h (𝒰.idx s)).2.2 t

/-- An isomorphism of actual groups preserves fixed-rank smoothness along their units. -/
theorem SmoothAlongUnitOfRank.of_iso {r : ℕ} (h : SmoothAlongUnitOfRank G r) (e : H ≅ G) :
    SmoothAlongUnitOfRank H r := by
  let v := e.hom.hom.hom.left
  have : IsIso v := (Over.forget S).map_isIso ((Grp.forget _).mapIso e).hom
  have hu (s : S) : v (H.identitySection s) = G.identitySection s := by
    rw [← Scheme.Hom.comp_apply, identitySection_naturality]
  have hsm : SmoothAlongUnit H := by
    intro s
    have hs := h.1 s
    rw [← Scheme.Hom.mem_smoothLocus, ← hu s, ← Scheme.Hom.mem_preimage,
      Scheme.Hom.preimage_smoothLocus_eq, Scheme.Hom.mem_smoothLocus,
      show v ≫ G.X.hom = H.X.hom from Over.w e.hom.hom.hom] at hs
    exact hs
  have : IsFinite (projection G 1) := finite_projection G 1
  have : Flat (projection G 1) := h.2.1
  have : IsIso (map e.hom 1) := inferInstanceAs (IsIso (mapIso e 1).hom)
  have hjet := map_projection e.hom 1
  have hflat : Flat (projection H 1) := hjet ▸ inferInstanceAs (Flat (map e.hom 1 ≫ projection G 1))
  refine ⟨hsm, hflat, ?_⟩
  intro s
  rw [← hjet, Scheme.Hom.finrank_comp_left_of_isIso, h.2.2]

end Rank

/-- Fixed-rank smoothness along the unit is stable under base change and group
isomorphisms and descends along base open covers. -/
def SmoothAlongUnitOfRankLocalityStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [IsSeparated G.X.hom]
    [LocallyOfFinitePresentation G.X.hom] (r : ℕ),
    (∀ (T : Scheme.{u}) (b : T ⟶ S), SmoothAlongUnitOfRank G r →
      SmoothAlongUnitOfRank ((GroupScheme.baseChange b).obj G) r) ∧
      (∀ 𝒰 : S.OpenCover.{v},
        (∀ i, SmoothAlongUnitOfRank ((GroupScheme.baseChange (𝒰.f i)).obj G) r) →
          SmoothAlongUnitOfRank G r) ∧
      ∀ (H : GroupScheme S), (H ≅ G) → SmoothAlongUnitOfRank G r → SmoothAlongUnitOfRank H r

theorem smoothAlongUnitOfRankLocality : SmoothAlongUnitOfRankLocalityStatement.{u, v} := by
  intro S G _ _ r
  exact ⟨fun _ b h => h.baseChange b, smoothAlongUnitOfRank_of_openCover,
    fun _ e h => h.of_iso e⟩

end Langlands.GroupScheme.IdentityJet
