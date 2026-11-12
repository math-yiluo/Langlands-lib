import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceFilteredRingPointStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.ProductPointsGluing
import Langlands.AlgebraicGeometry.AlgebraicSpace.EtalePresentationComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.AtlasRelation
import Langlands.AlgebraicGeometry.AlgebraicSpace.KernelPairDiagonal
import Langlands.AlgebraicGeometry.AffineLimitIsomorphismDescent
import Langlands.AlgebraicGeometry.SchemeLimitRelativePropertyProof
import Langlands.AlgebraicGeometry.ConstructibleAffineLimit
import Langlands.AlgebraicGeometry.SchemeFilteredModelExistenceProof
import Langlands.AlgebraicGeometry.SchemeLimitModelSpectrum
import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
import Mathlib.CategoryTheory.Filtered.Final

/-!
# Filtered colimits of ring-valued points of algebraic spaces: proof
-/

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace SpaceFilteredPoints

variable {S : Scheme.{u}}

/-- The section of a presheaf given by an actual scheme point of an atlas. -/
abbrev atlasSection {F : Presheaf S} {U : Over S} (a : (schemeYoneda S).obj U ⟶ F)
    {W : Over S} (u : W ⟶ U) : F.obj (op W) :=
  a.app (op W) (ULift.up u : ((schemeYoneda S).obj U).obj (op W))

theorem atlasSection_pullback {X : AlgebraicSpace S} {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ X.presheaf)
    {W W' : Over S} (f : W' ⟶ W) (u : W ⟶ U) :
    X.pullback f (atlasSection a u) = atlasSection a (f ≫ u) :=
  (NatTrans.naturality_apply a f.op (ULift.up u : ((schemeYoneda S).obj U).obj (op W))).symm

/-- A test scheme over `S` through a map to the underlying scheme of `T`. -/
abbrev overOf {T : Over S} {Z : Scheme.{u}} (f : Z ⟶ T.left) : Over S :=
  Over.mk (f ≫ T.hom)

/-- The corresponding morphism over `S`. -/
abbrev overHom {T : Over S} {Z : Scheme.{u}} (f : Z ⟶ T.left) : overOf f ⟶ T :=
  Over.homMk f rfl

/-- A single flat, locally finitely presented, surjective morphism generates an
fppf covering sieve of the slice. -/
theorem generate_singleton_mem_fppfTopology {W M : Over S} (q : W ⟶ M)
    [Flat q.left] [LocallyOfFinitePresentation q.left] [Surjective q.left] :
    Sieve.generate (Presieve.singleton q) ∈ fppfTopology S M := by
  change Sieve.overEquiv M (Sieve.generate (Presieve.singleton q)) ∈
    Scheme.fppfTopology M.left
  rw [← Presieve.ofArrows_pUnit.{0} q, ← Sieve.ofArrows,
    Sieve.overEquiv_ofArrows, Sieve.ofArrows, Presieve.ofArrows_pUnit]
  apply Precoverage.generate_mem_toGrothendieck
  exact (Scheme.singleton_mem_precoverage_iff
    (@Flat.{u} ⊓ @LocallyOfFinitePresentation.{u}) q.left).mpr
    ⟨(inferInstance : Surjective q.left).surj, ⟨inferInstance, inferInstance⟩⟩

variable (X : AlgebraicSpace S)

/-- The sheaf condition of a space for one fppf covering morphism. -/
theorem isSheafFor_singleton {W T : Over S} (e : W ⟶ T)
    [Flat e.left] [LocallyOfFinitePresentation e.left] [Surjective e.left] :
    Presieve.IsSheafFor X.presheaf (Presieve.singleton e) :=
  ProductPointsDescent.isSheafFor_singleton X e

/-- Pullback of sections along an fppf covering morphism is injective. -/
theorem pullback_injective {W T : Over S} (e : W ⟶ T)
    [Flat e.left] [LocallyOfFinitePresentation e.left] [Surjective e.left] :
    Function.Injective (X.pullback e) :=
  ProductPointsDescent.pullback_injective X e

/-- Sections compatible on all pairs of maps equalized by an fppf covering morphism
descend along it. -/
theorem exists_pullback_eq {W T : Over S} (e : W ⟶ T)
    [Flat e.left] [LocallyOfFinitePresentation e.left] [Surjective e.left]
    (z : X.sections W)
    (hz : ∀ {Z : Over S} (p₁ p₂ : Z ⟶ W), p₁ ≫ e = p₂ ≫ e →
      X.pullback p₁ z = X.pullback p₂ z) :
    ∃ y, X.pullback e y = z :=
  ((Presieve.isSheafFor_singleton.mp (isSheafFor_singleton X e)) z hz).exists

variable {X} {U : Over S} (a : (schemeYoneda S).obj U ⟶ X.presheaf)

/-- Every section is etale-locally the image of an actual atlas point. -/
theorem exists_atlas_lift (ha : IsEtale a) (hs : IsSurjective a) {T : Over S}
    (x : X.sections T) :
    ∃ (V : Over S) (p : V ⟶ T) (v : V ⟶ U), Etale p.left ∧ Surjective p.left ∧
      atlasSection a v = X.pullback p x := by
  let g : (schemeYoneda S).obj T ⟶ X.presheaf := uliftYonedaEquiv.symm x
  let p := ha.representable.snd g
  have hpe : Etale p.left :=
    ha.projection g (ha.representable.fst g) p (ha.representable.isPullback g)
  have hps : Surjective p.left :=
    hs.projection g (ha.representable.fst g) p (ha.representable.isPullback g)
  obtain ⟨v, hv⟩ := (schemeYoneda S).map_surjective (ha.representable.fst g)
  refine ⟨_, p, v, hpe, hps, ?_⟩
  have := congrArg (fun z : (schemeYoneda S).obj (ha.representable.pullback g) ⟶ X.presheaf =>
      z.app (op (ha.representable.pullback g)) ⟨𝟙 _⟩) (ha.representable.isPullback g).w
  simpa [g, ← hv] using this

/-- An etale surjective morphism onto a quasi-compact scheme is refined by one from
an affine scheme. -/
theorem exists_affine_refinement {V T : Scheme.{u}} (p : V ⟶ T) [Etale p] [Surjective p]
    [CompactSpace T] :
    ∃ (W : Scheme.{u}) (j : W ⟶ V), IsAffine W ∧ Etale (j ≫ p) ∧ Surjective (j ≫ p) := by
  classical
  let 𝒰 := V.affineCover
  let O : V → Set T := fun v => p '' Set.range (𝒰.f (𝒰.idx v))
  have hO : ∀ v, IsOpen (O v) := fun v =>
    p.isOpenMap _ (𝒰.f (𝒰.idx v)).isOpenEmbedding.isOpen_range
  have hcov : Set.univ ⊆ ⋃ v, O v := by
    intro t _
    obtain ⟨v, rfl⟩ := p.surjective t
    exact Set.mem_iUnion.mpr ⟨v, v, 𝒰.covers v, rfl⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover O hO hcov
  let Y : s → Scheme.{u} := fun v => 𝒰.X (𝒰.idx v.1)
  let j : ∐ Y ⟶ V := Sigma.desc fun v => 𝒰.f (𝒰.idx v.1)
  have hj : Etale j := IsZariskiLocalAtSource.sigmaDesc (fun _ => inferInstance)
  refine ⟨∐ Y, j, inferInstance, inferInstance, ⟨fun t => ?_⟩⟩
  obtain ⟨v, hv, ht⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ t))
  obtain ⟨_, ⟨y, rfl⟩, rfl⟩ := ht
  refine ⟨Sigma.ι Y ⟨v, hv⟩ y, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, Sigma.ι_comp_desc_assoc]

/-- Every section over a quasi-compact test scheme is, on an affine etale surjective
cover, the image of an actual atlas point. -/
theorem exists_affine_atlas_lift (ha : IsEtale a) (hs : IsSurjective a) {T : Over S}
    [CompactSpace T.left] (x : X.sections T) :
    ∃ (W : Over S) (e : W ⟶ T) (v : W ⟶ U), IsAffine W.left ∧ Etale e.left ∧
      Surjective e.left ∧ atlasSection a v = X.pullback e x := by
  obtain ⟨V, p, v, hpe, hps, hv⟩ := exists_atlas_lift a ha hs x
  obtain ⟨W, j, hW, hje, hjs⟩ := exists_affine_refinement p.left
  let W' : Over S := Over.mk (j ≫ V.hom)
  let j' : W' ⟶ V := Over.homMk j
  refine ⟨W', j' ≫ p, j' ≫ v, hW, hje, hjs, ?_⟩
  rw [← atlasSection_pullback, hv, X.pullback_comp]

/-- The represented kernel pair of an etale atlas, with its lifting property. -/
theorem exists_kernel_pair (ha : IsEtale a) :
    ∃ (R : Over S) (r₁ r₂ : R ⟶ U), Etale r₁.left ∧ Etale r₂.left ∧
      (∀ {Z : Over S} (f f' : Z ⟶ U), atlasSection a f = atlasSection a f' →
        ∃ r : Z ⟶ R, r ≫ r₁ = f ∧ r ≫ r₂ = f') ∧
      (∀ {Z : Over S} (r : Z ⟶ R), atlasSection a (r ≫ r₁) = atlasSection a (r ≫ r₂)) := by
  obtain ⟨R, r₁, r₂, h, -⟩ := AtlasRelation.exists_kernelPair a ha.representable
  refine ⟨R, r₁, r₂, ha.projection a _ r₁ h.flip, ha.projection a _ r₂ h, ?_, ?_⟩
  · intro Z f f' hff'
    have hw := KernelPair.map_comp_eq_of_app_eq a hff'
    obtain ⟨r, hr⟩ := (schemeYoneda S).map_surjective (h.lift _ _ hw)
    refine ⟨r, (schemeYoneda S).map_injective ?_, (schemeYoneda S).map_injective ?_⟩
    · rw [Functor.map_comp, hr, h.lift_fst]
    · rw [Functor.map_comp, hr, h.lift_snd]
  · intro Z r
    exact congrArg (fun φ : (schemeYoneda S).obj R ⟶ X.presheaf => φ.app (op Z) ⟨r⟩) h.w


/-- Transition maps of a target base change commute with the fixed projection. -/
@[reassoc]
theorem targetLimit_map_snd {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    {B T : Scheme.{u}} (t : D ⟶ (Functor.const I).obj B) (q : T ⟶ B) {i j : I} (f : i ⟶ j) :
    (TargetLimit.diagram D t q).map f ≫ pullback.snd (t.app j) q = pullback.snd (t.app i) q := by
  have := (TargetLimit.comparison D t q).naturality f
  simp only [Functor.const_obj_map] at this
  exact this

/-- Transition maps of a target base change lie over the original transition maps. -/
@[reassoc]
theorem targetLimit_map_fst {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    {B T : Scheme.{u}} (t : D ⟶ (Functor.const I).obj B) (q : T ⟶ B) {i j : I} (f : i ⟶ j) :
    (TargetLimit.diagram D t q).map f ≫ pullback.fst (t.app j) q =
      pullback.fst (t.app i) q ≫ D.map f :=
  (TargetLimit.projection D t q).naturality f

/-- **Eventual equality.** Let `D` be a cofiltered diagram of affine schemes over the
underlying affine scheme of a test scheme `T`, with limit `c`. If the atlas is locally of
finite type, two sections over `T` which agree over the limit agree over some stage. -/
theorem exists_eq_of_limit (ha : IsEtale a) (hs : IsSurjective a) [LocallyOfFiniteType U.hom]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u}) [∀ i, IsAffine (D.obj i)] {T : Over S} [IsAffine T.left]
    (t : D ⟶ (Functor.const I).obj T.left) (c : Cone D) (hc : IsLimit c)
    (p : c.pt ⟶ T.left) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (x y : X.sections T) (hxy : X.pullback (overHom p) x = X.pullback (overHom p) y) :
    ∃ i, X.pullback (overHom (t.app i)) x = X.pullback (overHom (t.app i)) y := by
  obtain ⟨W₁, e₁, v₁, hW₁, he₁, hs₁, hv₁⟩ := exists_affine_atlas_lift a ha hs x
  obtain ⟨W, e₂, v₂, hW, he₂, hs₂, hv₂⟩ := exists_affine_atlas_lift a ha hs (X.pullback e₁ y)
  obtain ⟨R, r₁, r₂, hr₁, hr₂, hlift, hcompat⟩ := exists_kernel_pair a ha
  let E : W ⟶ T := e₂ ≫ e₁
  have : Etale E.left := inferInstanceAs (Etale (e₂.left ≫ e₁.left))
  have : Surjective E.left := inferInstanceAs (Surjective (e₂.left ≫ e₁.left))
  have hEx : atlasSection a (e₂ ≫ v₁) = X.pullback E x := by
    rw [← atlasSection_pullback, hv₁, ← X.pullback_comp]
  have hEy : atlasSection a v₂ = X.pullback E y := by
    rw [hv₂, ← X.pullback_comp]
  -- The base change of the diagram along the affine cover of `T`.
  let Dw := TargetLimit.diagram D t E.left
  let C := TargetLimit.coneOfPullback D t E.left c p hp (IsPullback.of_hasPullback p E.left)
  let hC : IsLimit C := TargetLimit.isLimitConeOfPullback D t E.left c p hp _ hc
  -- The limit level.
  let Lo : Over S := Over.mk (pullback.snd p E.left ≫ W.hom)
  let σ : Lo ⟶ W := Over.homMk (pullback.snd p E.left) rfl
  let ρ : Lo ⟶ overOf p := Over.homMk (pullback.fst p E.left) (by
    simp only [overOf, Over.mk_hom, Lo]
    rw [pullback.condition_assoc, Over.w E])
  have hρσ : ρ ≫ overHom p = σ ≫ E := by
    ext1
    exact pullback.condition
  have hLo : atlasSection a (σ ≫ e₂ ≫ v₁) = atlasSection a (σ ≫ v₂) := by
    rw [← atlasSection_pullback a σ (e₂ ≫ v₁), ← atlasSection_pullback a σ v₂, hEx, hEy,
      ← X.pullback_comp, ← X.pullback_comp, ← hρσ, X.pullback_comp, X.pullback_comp, hxy]
  obtain ⟨r, hrr₁, hrr₂⟩ := hlift _ _ hLo
  -- Descend the kernel-pair point to a stage.
  let tU : Dw ⟶ (Functor.const I).obj U.left :=
    TargetLimit.comparison D t E.left ≫ (Functor.const I).map (e₂ ≫ v₁).left
  have : LocallyOfFinitePresentation r₁.left := inferInstance
  obtain ⟨i, g, hg₁, hg₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    Dw tU r₁.left C hC r.left (by
      ext j
      have := congrArg CommaMorphism.left hrr₁
      simp only [Over.comp_left] at this
      simp only [tU, NatTrans.comp_app, Functor.const_map_app, Functor.const_obj_obj,
        TargetLimit.comparison, C, TargetLimit.coneOfPullback_π_snd_assoc, this]
      rfl)
  let tS : Dw ⟶ (Functor.const I).obj S :=
    TargetLimit.comparison D t E.left ≫ (Functor.const I).map W.hom
  have hv₁w : (e₂ ≫ v₁).left ≫ U.hom = W.hom := Over.w (e₂ ≫ v₁)
  obtain ⟨k, hik, hk⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType
    Dw tS U.hom C hC (i := i) (g ≫ r₂.left) (pullback.snd (t.app i) E.left ≫ v₂.left)
    (by
      change pullback.snd (t.app i) E.left ≫ W.hom = _
      rw [Category.assoc, Over.w r₂, ← Over.w r₁, ← Category.assoc g, hg₂]
      simp only [tU, NatTrans.comp_app, Functor.const_map_app, TargetLimit.comparison,
        Category.assoc, hv₁w])
    (by
      change pullback.snd (t.app i) E.left ≫ W.hom = _
      rw [Category.assoc, Over.w v₂])
    (by
      have := congrArg CommaMorphism.left hrr₂
      simp only [Over.comp_left] at this
      rw [← Category.assoc, hg₁, this]
      simp only [C, TargetLimit.coneOfPullback_π_snd_assoc]
      rfl)
  -- The stage `k`.
  let Wk : Over S := Over.mk (pullback.fst (t.app k) E.left ≫ t.app k ≫ T.hom)
  let ek : Wk ⟶ overOf (t.app k) := Over.homMk (pullback.fst (t.app k) E.left) rfl
  let sk : Wk ⟶ W := Over.homMk (pullback.snd (t.app k) E.left) (by
    simp only [Wk, Over.mk_hom]
    rw [← Over.w E, pullback.condition_assoc])
  have hsk : pullback.snd (t.app k) E.left ≫ W.hom = Wk.hom := Over.w sk
  let gk : Wk ⟶ R := Over.homMk (Dw.map hik ≫ g) (by
    rw [← hsk, ← Over.w r₁, Category.assoc, ← Category.assoc g, hg₂]
    simp only [tU, NatTrans.comp_app, Functor.const_map_app, TargetLimit.comparison,
      ← Category.assoc, Dw, targetLimit_map_snd]
    simp only [Category.assoc, hv₁w])
  have hek : ek ≫ overHom (t.app k) = sk ≫ E := by
    ext1
    exact pullback.condition
  have hgk₁ : gk ≫ r₁ = sk ≫ e₂ ≫ v₁ := by
    ext1
    change (Dw.map hik ≫ g) ≫ r₁.left = pullback.snd (t.app k) E.left ≫ (e₂ ≫ v₁).left
    rw [Category.assoc, hg₂]
    simp only [tU, NatTrans.comp_app, Functor.const_map_app, TargetLimit.comparison,
      ← Category.assoc, Dw, targetLimit_map_snd]
  have hgk₂ : gk ≫ r₂ = sk ≫ v₂ := by
    ext1
    change (Dw.map hik ≫ g) ≫ r₂.left = pullback.snd (t.app k) E.left ≫ v₂.left
    rw [Category.assoc, hk, ← Category.assoc]
    exact congrArg (· ≫ v₂.left) (targetLimit_map_snd D t E.left hik)
  have : Etale ek.left := inferInstanceAs (Etale (pullback.fst (t.app k) E.left))
  have : Flat ek.left := inferInstanceAs (Flat (pullback.fst (t.app k) E.left))
  have : LocallyOfFinitePresentation ek.left := inferInstance
  have : Surjective ek.left := inferInstanceAs (Surjective (pullback.fst (t.app k) E.left))
  refine ⟨k, pullback_injective X ek ?_⟩
  rw [← X.pullback_comp, ← X.pullback_comp, hek, X.pullback_comp sk E x,
    X.pullback_comp sk E y, ← hEx, ← hEy, atlasSection_pullback, atlasSection_pullback,
    ← hgk₁, ← hgk₂, hcompat]

/-- Equality after a morphism persists after any morphism factoring through it. -/
theorem pullback_eq_of_comp {A B T : Over S} (f : A ⟶ T) (g : B ⟶ T) (ι : B ⟶ A)
    (h : ι ≫ f = g) {x y : X.sections T} (hxy : X.pullback f x = X.pullback f y) :
    X.pullback g x = X.pullback g y := by
  rw [← h, X.pullback_comp, X.pullback_comp, hxy]

/-- Pulling back an atlas point along a morphism that factors through a second atlas
point lifting `x` gives the pullback of `x`. -/
theorem pullback_atlasSection_eq {A V W T : Over S} (f : A ⟶ V) (v : V ⟶ U) (μ : A ⟶ W)
    (w : W ⟶ U) (e : W ⟶ T) {x : X.sections T} (hw : atlasSection a w = X.pullback e x)
    (h : f ≫ v = μ ≫ w) :
    X.pullback f (atlasSection a v) = X.pullback (μ ≫ e) x := by
  rw [atlasSection_pullback, h, ← atlasSection_pullback, hw, X.pullback_comp]

section Restriction

variable {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u}) (i : I)

/-- The diagram restricted to the indices over a fixed index. -/
abbrev overDiagram : Over i ⥤ Scheme.{u} := Over.forget i ⋙ D

/-- Its transition maps to the fixed stage. -/
def overStructure : overDiagram D i ⟶ (Functor.const (Over i)).obj (D.obj i) where
  app k := D.map k.hom
  naturality k l f := by
    dsimp
    rw [Category.comp_id, ← D.map_comp, Over.w f]

@[simp]
theorem overStructure_app (k : Over i) : (overStructure D i).app k = D.map k.hom := rfl

instance [∀ j, IsAffine (D.obj j)] (k : Over i) : IsAffine ((overDiagram D i).obj k) :=
  inferInstanceAs (IsAffine (D.obj k.left))

variable {D} (c : Cone D)

theorem overCone_π_comp (k : Over i) :
    (c.whisker (Over.forget i)).π.app k ≫ (overStructure D i).app k = c.π.app i :=
  c.w k.hom

/-- The restricted cone of a cofiltered limit is a limit. -/
def overConeIsLimit [IsCofiltered I] (hc : IsLimit c) : IsLimit (c.whisker (Over.forget i)) :=
  (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc

end Restriction

/-- The transition maps of a target base change are base changes of the original
transition maps. -/
theorem targetLimit_isPullback_map {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    {B T : Scheme.{u}} (t : D ⟶ (Functor.const I).obj B) (q : T ⟶ B) {i j : I} (f : i ⟶ j) :
    IsPullback ((TargetLimit.diagram D t q).map f) (pullback.fst (t.app i) q)
      (pullback.fst (t.app j) q) (D.map f) := by
  have ht : D.map f ≫ t.app j = t.app i := by
    have := t.naturality f
    simp only [Functor.const_obj_map] at this
    exact this
  refine IsPullback.of_right (h₁₂ := pullback.snd (t.app j) q) (v₁₃ := q) (h₂₂ := t.app j)
    ?_ (targetLimit_map_fst D t q f) (IsPullback.of_hasPullback (t.app j) q).flip
  rw [targetLimit_map_snd, ht]
  exact (IsPullback.of_hasPullback (t.app i) q).flip

instance targetLimit_isAffineHom_map {I : Type u} [Category.{u} I] (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    {B T : Scheme.{u}} (t : D ⟶ (Functor.const I).obj B) (q : T ⟶ B) {i j : I} (f : i ⟶ j) :
    IsAffineHom ((TargetLimit.diagram D t q).map f) :=
  MorphismProperty.of_isPullback (P := @IsAffineHom) (targetLimit_isPullback_map D t q f).flip
    inferInstance

section Model

variable {I : Type u} [Category.{u} I] {D : I ⥤ Scheme.{u}} (c : Cone D)
  {W V : Scheme.{u}} {g : W ⟶ c.pt} {i : I} {q : V ⟶ D.obj i} {π : W ⟶ V}

/-- The comparison map of a model into its base change along a transition map. -/
abbrev modelLift (hpb : IsPullback π g q (c.π.app i)) {j : I} (f : j ⟶ i) :
    W ⟶ Limits.pullback (D.map f) q :=
  pullback.lift (g ≫ c.π.app j) π (by rw [Category.assoc, c.w f, hpb.w])

/-- A model at a stage base changes to a model at every later stage. -/
theorem isPullback_modelLift (hpb : IsPullback π g q (c.π.app i)) {j : I} (f : j ⟶ i) :
    IsPullback (modelLift c hpb f) g (pullback.fst (D.map f) q) (c.π.app j) := by
  refine IsPullback.of_right (h₁₂ := pullback.snd (D.map f) q) (v₁₃ := q) (h₂₂ := D.map f)
    ?_ (pullback.lift_fst _ _ _) (IsPullback.of_hasPullback (D.map f) q).flip
  rw [pullback.lift_snd, c.w f]
  exact hpb

end Model

/-- **Descent from a flat model.** Let `x` be a section over the limit, lifted to an atlas
point `w` on an etale cover `e`. If `e` is the base change of a flat, locally finitely
presented, surjective morphism `q` from an affine scheme at some stage, and `w` comes
from an atlas point `v` of the model, then `x` comes from a stage. -/
theorem exists_stage_of_model (ha : IsEtale a) (hs : IsSurjective a) [LocallyOfFiniteType U.hom]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    {D : I ⥤ Scheme.{u}} [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const I).obj S) {c : Cone D} (hc : IsLimit c)
    (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (x : X.sections (Over.mk p)) {W : Over S} (e : W ⟶ Over.mk p)
    [Etale e.left] [Surjective e.left]
    (w : W ⟶ U) (hw : atlasSection a w = X.pullback e x)
    (k : I) {V : Scheme.{u}} [IsAffine V] (q : V ⟶ D.obj k)
    [Flat q] [LocallyOfFinitePresentation q] [Surjective q]
    (π : W.left ⟶ V) (hpb : IsPullback π e.left q (c.π.app k))
    (v : V ⟶ U.left) (hv : π ≫ v = w.left) (hvU : v ≫ U.hom = q ≫ t.app k) :
    ∃ (j : I) (y : X.sections (Over.mk (t.app j))),
      X.pullback (Over.homMk (c.π.app j) (hp j) : Over.mk p ⟶ Over.mk (t.app j)) y = x := by
  let VV : Over S := Over.mk (q ≫ t.app k)
  let vV : VV ⟶ U := Over.homMk v hvU
  let gP : Limits.pullback q q ⟶ D.obj k := pullback.fst q q ≫ q
  let TP : Over S := Over.mk (gP ≫ t.app k)
  have : IsAffine TP.left := inferInstanceAs (IsAffine (Limits.pullback q q))
  let pr₁ : TP ⟶ VV := Over.homMk (pullback.fst q q) (by
    simp only [TP, VV, gP, Over.mk_hom, Category.assoc])
  let pr₂ : TP ⟶ VV := Over.homMk (pullback.snd q q) (by
    simp only [TP, VV, gP, Over.mk_hom, Category.assoc]
    rw [pullback.condition_assoc])
  -- The diagram of base changes of the model kernel pair.
  let D' := overDiagram D k
  let t' := overStructure D k
  let c' := c.whisker (Over.forget k)
  have hc' : IsLimit c' := overConeIsLimit k c hc
  let Dq := TargetLimit.diagram D' t' gP
  let tq := TargetLimit.comparison D' t' gP
  let pL := pullback.snd (c.π.app k) gP
  let Cq := TargetLimit.coneOfPullback D' t' gP c' (c.π.app k) (overCone_π_comp k c)
    (IsPullback.of_hasPullback (c.π.app k) gP)
  have hCq : IsLimit Cq := TargetLimit.isLimitConeOfPullback D' t' gP c' (c.π.app k)
    (overCone_π_comp k c) _ hc'
  have hpq : ∀ l, Cq.π.app l ≫ tq.app l = pL := fun l =>
    TargetLimit.coneOfPullback_π_snd D' t' gP c' (c.π.app k) (overCone_π_comp k c) _ l
  -- The two pullbacks of the model point agree over the limit.
  obtain ⟨l, hl⟩ := exists_eq_of_limit a ha hs Dq (T := TP) tq Cq hCq pL hpq
    (X.pullback pr₁ (atlasSection a vV)) (X.pullback pr₂ (atlasSection a vV)) (by
      have hc₁ : (pL ≫ pullback.fst q q) ≫ q = pullback.fst (c.π.app k) gP ≫ c.π.app k := by
        rw [Category.assoc]
        exact (pullback.condition (f := c.π.app k) (g := gP)).symm
      have hc₂ : (pL ≫ pullback.snd q q) ≫ q = pullback.fst (c.π.app k) gP ≫ c.π.app k := by
        rw [Category.assoc, ← pullback.condition]
        exact (pullback.condition (f := c.π.app k) (g := gP)).symm
      have hμ : ∀ μ : Limits.pullback (c.π.app k) gP ⟶ W.left,
          μ ≫ e.left = pullback.fst (c.π.app k) gP →
            μ ≫ W.hom = (overOf (T := TP) pL).hom := by
        intro μ hμ
        rw [← Over.w e, ← Category.assoc, hμ]
        change pullback.fst (c.π.app k) gP ≫ p = pL ≫ gP ≫ t.app k
        rw [← hp k, ← Category.assoc, pullback.condition, Category.assoc]
      let μ₁' : overOf (T := TP) pL ⟶ W :=
        Over.homMk (hpb.lift _ _ hc₁) (hμ _ (hpb.lift_snd _ _ _))
      let μ₂' : overOf (T := TP) pL ⟶ W :=
        Over.homMk (hpb.lift _ _ hc₂) (hμ _ (hpb.lift_snd _ _ _))
      have h₁ : (overHom (T := TP) pL ≫ pr₁) ≫ vV = μ₁' ≫ w := by
        ext1
        change (pL ≫ pullback.fst q q) ≫ v = hpb.lift _ _ hc₁ ≫ w.left
        rw [← hv, ← Category.assoc, hpb.lift_fst]
      have h₂ : (overHom (T := TP) pL ≫ pr₂) ≫ vV = μ₂' ≫ w := by
        ext1
        change (pL ≫ pullback.snd q q) ≫ v = hpb.lift _ _ hc₂ ≫ w.left
        rw [← hv, ← Category.assoc, hpb.lift_fst]
      have he : μ₁' ≫ e = μ₂' ≫ e := by
        ext1
        change hpb.lift _ _ hc₁ ≫ e.left = hpb.lift _ _ hc₂ ≫ e.left
        rw [hpb.lift_snd, hpb.lift_snd]
      rw [← X.pullback_comp, ← X.pullback_comp,
        pullback_atlasSection_eq a _ vV μ₁' w e hw h₁,
        pullback_atlasSection_eq a _ vV μ₂' w e hw h₂, he])
  -- Glue the model point over the stage `l`.
  have htl : D.map l.hom ≫ t.app k = t.app l.left := by
    have := t.naturality l.hom
    simp only [Functor.const_obj_map] at this
    exact this
  let Vl : Over S := Over.mk (pullback.fst (D.map l.hom) q ≫ t.app l.left)
  let ql : Vl ⟶ Over.mk (t.app l.left) := Over.homMk (pullback.fst (D.map l.hom) q) rfl
  let sl : Vl ⟶ VV := Over.homMk (pullback.snd (D.map l.hom) q) (by
    change pullback.snd (D.map l.hom) q ≫ q ≫ t.app k =
      pullback.fst (D.map l.hom) q ≫ t.app l.left
    rw [← pullback.condition_assoc, htl])
  have : Flat ql.left := inferInstanceAs (Flat (pullback.fst (D.map l.hom) q))
  have : LocallyOfFinitePresentation ql.left :=
    inferInstanceAs (LocallyOfFinitePresentation (pullback.fst (D.map l.hom) q))
  have : Surjective ql.left := inferInstanceAs (Surjective (pullback.fst (D.map l.hom) q))
  obtain ⟨y, hy⟩ := exists_pullback_eq X ql (X.pullback sl (atlasSection a vV)) (by
    intro Z p₁ p₂ h12
    have h12' : p₁.left ≫ pullback.fst (D.map l.hom) q =
        p₂.left ≫ pullback.fst (D.map l.hom) q :=
      congrArg CommaMorphism.left h12
    obtain ⟨ζ, hζ₁, hζ₂, hζ₃⟩ : ∃ ζ : Z.left ⟶ Limits.pullback (D.map l.hom) gP,
        ζ ≫ pullback.fst (D.map l.hom) gP = p₁.left ≫ pullback.fst (D.map l.hom) q ∧
        ζ ≫ pullback.snd (D.map l.hom) gP ≫ pullback.fst q q =
          p₁.left ≫ pullback.snd (D.map l.hom) q ∧
        ζ ≫ pullback.snd (D.map l.hom) gP ≫ pullback.snd q q =
          p₂.left ≫ pullback.snd (D.map l.hom) q := by
      have hin : (p₁.left ≫ pullback.snd (D.map l.hom) q) ≫ q =
          (p₂.left ≫ pullback.snd (D.map l.hom) q) ≫ q := by
        simp only [Category.assoc]
        rw [← pullback.condition, reassoc_of% h12']
      have hout : (p₁.left ≫ pullback.fst (D.map l.hom) q) ≫ D.map l.hom =
          pullback.lift _ _ hin ≫ gP := by
        simp only [gP, Category.assoc, pullback.lift_fst_assoc]
        rw [pullback.condition]
      exact ⟨pullback.lift _ _ hout, pullback.lift_fst _ _ _,
        by rw [pullback.lift_snd_assoc, pullback.lift_fst],
        by rw [pullback.lift_snd_assoc, pullback.lift_snd]⟩
    let ζ' : Z ⟶ overOf (T := TP) (tq.app l) := Over.homMk ζ (by
      rw [← Over.w p₁]
      change ζ ≫ pullback.snd (D.map l.hom) gP ≫ (pullback.fst q q ≫ q) ≫ t.app k =
        p₁.left ≫ pullback.fst (D.map l.hom) q ≫ t.app l.left
      rw [Category.assoc, reassoc_of% hζ₂, ← htl, ← pullback.condition_assoc])
    have hp₁ : p₁ ≫ sl = ζ' ≫ overHom (T := TP) (tq.app l) ≫ pr₁ := by
      ext1
      exact hζ₂.symm
    have hp₂ : p₂ ≫ sl = ζ' ≫ overHom (T := TP) (tq.app l) ≫ pr₂ := by
      ext1
      exact hζ₃.symm
    rw [← X.pullback_comp, ← X.pullback_comp, hp₁, hp₂]
    simp only [X.pullback_comp]
    rw [hl])
  refine ⟨l.left, y, ?_⟩
  let πl : W ⟶ Vl := Over.homMk (modelLift c hpb l.hom) (by
    change modelLift c hpb l.hom ≫ pullback.fst (D.map l.hom) q ≫ t.app l.left = W.hom
    rw [pullback.lift_fst_assoc, Category.assoc, hp, ← Over.w e]
    rfl)
  have h1 : e ≫ (Over.homMk (c.π.app l.left) (hp l.left) :
      Over.mk p ⟶ Over.mk (t.app l.left)) = πl ≫ ql := by
    ext1
    exact (pullback.lift_fst _ _ _).symm
  have h2 : πl ≫ sl ≫ vV = w := by
    ext1
    change modelLift c hpb l.hom ≫ pullback.snd (D.map l.hom) q ≫ v = w.left
    rw [pullback.lift_snd_assoc, hv]
  apply pullback_injective X e
  rw [← X.pullback_comp, h1, X.pullback_comp, hy, ← X.pullback_comp, atlasSection_pullback,
    Category.assoc, h2, hw]

section Steps

variable {I : Type u} [SmallCategory I] [IsCofiltered I] {D : I ⥤ Scheme.{u}}
  [∀ i, IsAffine (D.obj i)] {c : Cone D} (hc : IsLimit c)
  {W V : Scheme.{u}} {g : W ⟶ c.pt} {i : I} {q : V ⟶ D.obj i} {π : W ⟶ V}

include hc in
/-- A quasi-compact, quasi-separated model of an affine scheme becomes affine at a
later stage. -/
theorem exists_isAffine_model [IsAffine W] [QuasiCompact q] [QuasiSeparated q]
    (hpb : IsPullback π g q (c.π.app i)) :
    ∃ (j : I) (f : j ⟶ i), IsAffine (Limits.pullback (D.map f) q) := by
  let Dw := TargetLimit.diagram (overDiagram D i) (overStructure D i) q
  let Cw := TargetLimit.coneOfPullback (overDiagram D i) (overStructure D i) q
    (c.whisker (Over.forget i)) (c.π.app i) (overCone_π_comp i c) hpb.flip
  have hCw : IsLimit Cw := TargetLimit.isLimitConeOfPullback _ _ _ _ _ _ _
    (overConeIsLimit i c hc)
  have (l : Over i) : CompactSpace (Dw.obj l) :=
    inferInstanceAs (CompactSpace ↥(Limits.pullback (D.map l.hom) q))
  have (l : Over i) : QuasiSeparatedSpace (Dw.obj l) :=
    quasiSeparatedSpace_of_quasiSeparated (pullback.fst (D.map l.hom) q)
  have : IsAffine Cw.pt := inferInstanceAs (IsAffine W)
  obtain ⟨l, hl⟩ := Scheme.exists_isAffine_of_isLimit Dw Cw hCw
  exact ⟨l.left, l.hom, hl⟩

include hc in
/-- A finitely presented model of a flat morphism becomes flat at a later stage. -/
theorem exists_flat_model [Flat g] [LocallyOfFinitePresentation q] [QuasiCompact q]
    [QuasiSeparated q] (hpb : IsPullback π g q (c.π.app i)) :
    ∃ (j : I) (f : j ⟶ i), Flat (pullback.fst (D.map f) q) := by
  have hw : q ≫ 𝟙 (D.obj i) = q := Category.comp_id q
  have H : Flat (AffineLimit.baseChangeMap q (𝟙 _) q hw (c.π.app i)) := by
    have h₁ : Flat (pullback.fst (c.π.app i) q) := by
      rw [← hpb.flip.isoPullback_inv_fst]
      exact MorphismProperty.RespectsIso.precomp @Flat _ _ inferInstance
    rw [← MorphismProperty.cancel_right_of_respectsIso @Flat _
      (pullback.fst (c.π.app i) (𝟙 _)), AffineLimit.baseChangeMap_fst]
    exact h₁
  obtain ⟨l, hl⟩ := (AffineLimit.relativeFlatDescent (overDiagram D i) (overStructure D i)
    q (𝟙 _) q hw (c.whisker (Over.forget i)) (overConeIsLimit i c hc) (c.π.app i)
    (overCone_π_comp i c)).mp H
  refine ⟨l.left, l.hom, ?_⟩
  have : Flat (AffineLimit.baseChangeMap q (𝟙 _) q hw (D.map l.hom)) := hl
  rw [← AffineLimit.baseChangeMap_fst q (𝟙 _) q hw (D.map l.hom)]
  exact (MorphismProperty.cancel_right_of_respectsIso @Flat _ _).mpr this

include hc in
/-- A finitely presented model of a surjective morphism becomes surjective at a later
stage. -/
theorem exists_surjective_model [Surjective g] [LocallyOfFinitePresentation q]
    [QuasiCompact q] (hpb : IsPullback π g q (c.π.app i)) :
    ∃ (j : I) (f : j ⟶ i), Surjective (pullback.fst (D.map f) q) := by
  have hcons : Topology.IsConstructible (Set.range q) := by
    rw [← Set.image_univ]
    exact q.isConstructible_image Topology.IsConstructible.univ
  obtain ⟨j, f, hf⟩ := SchemeFiberGeometry.exists_map_preimage_eq_univ_of_isConstructible
    D c hc i (Set.range q) hcons (by
      ext x
      simp only [Set.mem_preimage, Set.mem_univ, iff_true]
      obtain ⟨y, rfl⟩ := g.surjective x
      exact ⟨π y, by rw [← Scheme.Hom.comp_apply, hpb.w]; rfl⟩)
  refine ⟨j, f, ⟨fun x => ?_⟩⟩
  have : x ∈ Set.range (pullback.fst (D.map f) q) := by
    rw [Scheme.Pullback.range_fst, hf]
    trivial
  exact this

include hc in
/-- On an affine model, a morphism from the limit model to a locally finitely presented
scheme over the base comes from a later stage of the model. -/
theorem exists_lift_model [IsAffine V] {B T : Scheme.{u}} (t : D ⟶ (Functor.const I).obj B)
    (p : c.pt ⟶ B) (hp : ∀ i, c.π.app i ≫ t.app i = p) (r : T ⟶ B)
    [LocallyOfFinitePresentation r] (b : W ⟶ T) (hb : b ≫ r = g ≫ p)
    (hpb : IsPullback π g q (c.π.app i)) :
    ∃ (j : I) (f : j ⟶ i) (h : Limits.pullback (D.map f) q ⟶ T),
      modelLift c hpb f ≫ h = b ∧ h ≫ r = pullback.fst (D.map f) q ≫ t.app j := by
  let Dw := TargetLimit.diagram (overDiagram D i) (overStructure D i) q
  let tS : Dw ⟶ (Functor.const (Over i)).obj B :=
    TargetLimit.comparison (overDiagram D i) (overStructure D i) q ≫
      (Functor.const (Over i)).map (q ≫ t.app i)
  let Cw := TargetLimit.coneOfPullback (overDiagram D i) (overStructure D i) q
    (c.whisker (Over.forget i)) (c.π.app i) (overCone_π_comp i c) hpb.flip
  have hCw : IsLimit Cw := TargetLimit.isLimitConeOfPullback _ _ _ _ _ _ _
    (overConeIsLimit i c hc)
  obtain ⟨l, h, hh₁, hh₂⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation
    Dw tS r Cw hCw b (by
      ext l
      simp only [tS, NatTrans.comp_app, Functor.const_map_app, TargetLimit.comparison, Cw,
        TargetLimit.coneOfPullback_π_snd_assoc]
      rw [hb, ← hp i, hpb.w_assoc])
  have hπ : (Cw.π.app l : W ⟶ Limits.pullback (D.map l.hom) q) = modelLift c hpb l.hom := by
    apply pullback.hom_ext
    · exact (TargetLimit.coneOfPullback_π_fst (overDiagram D i) (overStructure D i) q
        (c.whisker (Over.forget i)) (c.π.app i) (overCone_π_comp i c) hpb.flip l).trans
        (pullback.lift_fst _ _ _).symm
    · exact (TargetLimit.coneOfPullback_π_snd (overDiagram D i) (overStructure D i) q
        (c.whisker (Over.forget i)) (c.π.app i) (overCone_π_comp i c) hpb.flip l).trans
        (pullback.lift_snd _ _ _).symm
  have htl : D.map l.hom ≫ t.app i = t.app l.left := by
    have := t.naturality l.hom
    simp only [Functor.const_obj_map] at this
    exact this
  refine ⟨l.left, l.hom, h, by rw [← hπ]; exact hh₁, ?_⟩
  rw [hh₂]
  change pullback.snd (D.map l.hom) q ≫ q ≫ t.app i = _
  rw [← pullback.condition_assoc, htl]

end Steps

/-- **Sections over the limit come from a stage.** Under a locally finitely presented
atlas, for a cofiltered diagram of affine schemes over `S` with affine limit in which
finitely presented affine schemes over the limit have finitely presented models at a
stage, every section over the limit comes from a stage. -/
theorem exists_stage (ha : IsEtale a) (hs : IsSurjective a) [LocallyOfFinitePresentation U.hom]
    {I : Type u} [SmallCategory I] [IsCofiltered I]
    {D : I ⥤ Scheme.{u}} [∀ i, IsAffine (D.obj i)]
    (t : D ⟶ (Functor.const I).obj S) {c : Cone D} (hc : IsLimit c) [IsAffine c.pt]
    (p : c.pt ⟶ S) (hp : ∀ i, c.π.app i ≫ t.app i = p)
    (hmodel : ∀ (W : Scheme.{u}) [IsAffine W] (g : W ⟶ c.pt) [LocallyOfFinitePresentation g],
      ∃ (i : I) (V : Scheme.{u}) (q : V ⟶ D.obj i) (π : W ⟶ V),
        LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q ∧
          IsPullback π g q (c.π.app i))
    (x : X.sections (Over.mk p)) :
    ∃ (j : I) (y : X.sections (Over.mk (t.app j))),
      X.pullback (Over.homMk (c.π.app j) (hp j) : Over.mk p ⟶ Over.mk (t.app j)) y = x := by
  have : CompactSpace (Over.mk p).left := inferInstanceAs (CompactSpace c.pt)
  obtain ⟨W, e, w, hW, he, hes, hw⟩ := exists_affine_atlas_lift a ha hs x
  have : LocallyOfFiniteType U.hom := inferInstance
  obtain ⟨i₀, V₀, q₀, π₀, h₀, h₀', h₀'', hpb₀⟩ := hmodel W.left e.left
  -- An affine model.
  obtain ⟨i₁, f₁, hV₁⟩ := exists_isAffine_model hc hpb₀
  have hpb₁ := isPullback_modelLift c hpb₀ f₁
  -- A flat model.
  obtain ⟨i₂, f₂, hfl₂⟩ := exists_flat_model hc hpb₁
  have hpb₂ := isPullback_modelLift c hpb₁ f₂
  -- A surjective model.
  obtain ⟨i₃, f₃, hsu₃⟩ := exists_surjective_model hc hpb₂
  have hpb₃ := isPullback_modelLift c hpb₂ f₃
  -- The atlas point on a model.
  obtain ⟨i₄, f₄, v, hv, hvU⟩ := exists_lift_model hc t p hp U.hom w.left
    (by rw [Over.w w, ← Over.w e]; rfl) hpb₃
  have hpb₄ := isPullback_modelLift c hpb₃ f₄
  exact exists_stage_of_model a ha hs t hc p hp x e w hw i₄ _ _ hpb₄ v hv hvU

end SpaceFilteredPoints


namespace SpaceFilteredRingPoints

open SpaceFilteredPoints SchemeLimitModel
open Langlands.AlgebraicGeometry.PointTopology (ringTest ringTestMap ringTestMap_comp)

variable {R : Type u} [CommRing R] {X : AlgebraicSpace (Spec (CommRingCat.of R))}

/-- Change of coefficient algebra is compatible with composition. -/
theorem changeRing_comp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B] [Algebra R C] (f : A →ₐ[R] B) (g : B →ₐ[R] C)
    (x : RingPoints R X A) :
    RingPoints.changeRing (g.comp f) x =
      RingPoints.changeRing g (RingPoints.changeRing f x) := by
  unfold RingPoints.changeRing
  rw [ringTestMap_comp, X.pullback_comp]

variable {J : Type u} [SmallCategory J] (F : J ⥤ CommAlgCat.{u} R) (c : Cocone F)

/-- Changing a stage point to a later stage and then to the colimit is changing it to the
colimit directly. -/
theorem changeRing_cocone {a b : J} (f : a ⟶ b) (x : RingPoints R X (F.obj a)) :
    RingPoints.changeRing (c.ι.app b).hom (RingPoints.changeRing (F.map f).hom x) =
      RingPoints.changeRing (c.ι.app a).hom x := by
  rw [← changeRing_comp, ← CommAlgCat.hom_comp, c.w]

variable [IsFiltered J] (hc : IsColimit c)

include hc in
/-- Two points at one stage which agree over the colimit agree at a later stage. -/
theorem exists_changeRing_eq (hX : LocallyOfFiniteTypeOverBase X) (m : J)
    (p q : RingPoints R X (F.obj m))
    (hpq : RingPoints.changeRing (c.ι.app m).hom p = RingPoints.changeRing (c.ι.app m).hom q) :
    ∃ (k : J) (φ : m ⟶ k),
      RingPoints.changeRing (F.map φ).hom p = RingPoints.changeRing (F.map φ).hom q := by
  obtain ⟨U, a, ha, hs, hU⟩ := hX.exists_atlas
  have : IsAffine (ringTest R (F.obj m)).left := by
    change IsAffine (Spec _)
    infer_instance
  have hlim : X.pullback (overHom (T := ringTest R (F.obj m))
        ((spectrumCone R F c).π.app (op m))) p =
      X.pullback (overHom (T := ringTest R (F.obj m))
        ((spectrumCone R F c).π.app (op m))) q := by
    refine pullback_eq_of_comp (ringTestMap R (c.ι.app m).hom) _
      (Over.homMk (𝟙 _) ?_ : overOf (T := ringTest R (F.obj m))
        ((spectrumCone R F c).π.app (op m)) ⟶ ringTest R c.pt) ?_ hpq
    · exact (Category.id_comp _).trans (Over.w (ringTestMap R (c.ι.app m).hom)).symm
    · ext1
      exact Category.id_comp _
  obtain ⟨l, hl⟩ := exists_eq_of_limit a ha hs (overDiagram (spectrumDiagram R F) (op m))
    (T := ringTest R (F.obj m)) (overStructure (spectrumDiagram R F) (op m))
    ((spectrumCone R F c).whisker (Over.forget (op m)))
    (overConeIsLimit (op m) (spectrumCone R F c) (spectrumConeIsLimit R F c hc))
    ((spectrumCone R F c).π.app (op m)) (overCone_π_comp (op m) (spectrumCone R F c)) p q hlim
  refine ⟨l.left.unop, l.hom.unop, ?_⟩
  refine pullback_eq_of_comp _ (ringTestMap R (F.map l.hom.unop).hom)
    (Over.homMk (𝟙 _) ?_ : ringTest R (F.obj l.left.unop) ⟶ overOf (T := ringTest R (F.obj m))
      ((overStructure (spectrumDiagram R F) (op m)).app l)) ?_ hl
  · exact (Category.id_comp _).trans (Over.w (ringTestMap R (F.map l.hom.unop).hom))
  · ext1
    exact Category.id_comp _

include hc in
/-- Finitely presented affine schemes over the colimit spectrum have finitely presented
models over a stage spectrum. -/
theorem spectrum_model (W : Scheme.{u}) [IsAffine W] (g : W ⟶ (spectrumCone R F c).pt)
    [LocallyOfFinitePresentation g] :
    ∃ (i : Jᵒᵖ) (V : Scheme.{u}) (q : V ⟶ (spectrumDiagram R F).obj i) (π : W ⟶ V),
      LocallyOfFinitePresentation q ∧ QuasiCompact q ∧ QuasiSeparated q ∧
        IsPullback π g q ((spectrumCone R F c).π.app i) := by
  let Q : CommAlgCat.{u} R ⥤ CommRingCat.{u} :=
    (commAlgCatEquivUnder (CommRingCat.of R)).functor ⋙ Under.forget (CommRingCat.of R)
  let c' : Cocone (F ⋙ Q) := Q.mapCocone c
  let hc' : IsColimit c' := isColimitOfPreserves Q hc
  have : IsAffine (spectrumCone R F c).pt := by
    change IsAffine (Spec _)
    infer_instance
  have hqc : QuasiCompact g := inferInstance
  have hqs : QuasiSeparated g := inferInstance
  obtain ⟨j, Xj, gj, π, hfp, hqc, hqs, hpb⟩ :=
    @schemeFilteredModelExistence.{u} J _ _ (F ⋙ Q) c' hc' W g hqc hqs ‹_›
  exact ⟨op j, Xj, gj, π, hfp, hqc, hqs, hpb⟩

include hc in
/-- Every point over the colimit comes from a stage. -/
theorem exists_changeRing_eq_of_colimit (hX : LocallyOfFinitePresentationOverBase X)
    (p : RingPoints R X c.pt) :
    ∃ (i : J) (q : RingPoints R X (F.obj i)), RingPoints.changeRing (c.ι.app i).hom q = p := by
  obtain ⟨U, a, ha, hs, hU⟩ := hX.exists_atlas
  have : IsAffine (spectrumCone R F c).pt := by
    change IsAffine (Spec _)
    infer_instance
  obtain ⟨j, y, hy⟩ := exists_stage a ha hs (spectrumStructure R F) (spectrumConeIsLimit R F c hc)
    (spectrumBaseMap R F c) (spectrumCone_compat R F c) (spectrum_model F c hc) p
  exact ⟨j.unop, y, hy⟩

end SpaceFilteredRingPoints

open SpaceFilteredRingPoints in
/-- **Conrad, Theorem 3.4 for algebraic spaces (printed p.13 and p.17).** Points of an
algebraic space over `Spec R` along a filtered colimit of `R`-algebras. -/
theorem spaceFilteredRingPointComparison : SpaceFilteredRingPointComparison.{u} := by
  intro R _ J _ _ F c hc X
  refine ⟨fun hX i j p q => ⟨fun hpq => ?_, fun ⟨k, f, g, hfg⟩ => ?_⟩,
    fun hX p => exists_changeRing_eq_of_colimit F c hc hX p⟩
  · obtain ⟨k, φ, hk⟩ := exists_changeRing_eq F c hc hX (IsFiltered.max i j)
      (RingPoints.changeRing (F.map (IsFiltered.leftToMax i j)).hom p)
      (RingPoints.changeRing (F.map (IsFiltered.rightToMax i j)).hom q)
      (by rw [changeRing_cocone, changeRing_cocone, hpq])
    refine ⟨k, IsFiltered.leftToMax i j ≫ φ, IsFiltered.rightToMax i j ≫ φ, ?_⟩
    rw [F.map_comp, F.map_comp, CommAlgCat.hom_comp, CommAlgCat.hom_comp, changeRing_comp,
      changeRing_comp, hk]
  · rw [← changeRing_cocone F c f, ← changeRing_cocone F c g, hfg]

end Langlands.AlgebraicGeometry.AlgebraicSpace
