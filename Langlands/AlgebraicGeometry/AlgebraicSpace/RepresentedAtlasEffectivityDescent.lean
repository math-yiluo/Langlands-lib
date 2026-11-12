import Langlands.AlgebraicGeometry.AlgebraicSpace.RepresentedAtlasEffectivityStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.FppfQuotientRepresentability
import Langlands.AlgebraicGeometry.AlgebraicSpace.OpenChartGluingProof
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationKernelPair

/-! # Representability of a space morphism from one represented atlas pullback -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace AtlasEffectivity

variable {S : Scheme.{u}}

/-- Sections of a presheaf pullback are pairs of sections with equal images. -/
theorem exists_app_of_isPullback {P A B C : Presheaf S} {fst : P ⟶ A} {snd : P ⟶ B}
    {f : A ⟶ C} {g : B ⟶ C} (h : IsPullback fst snd f g) (T : Over S) (x : A.obj (op T))
    (y : B.obj (op T)) (hxy : f.app (op T) x = g.app (op T) y) :
    ∃ z, fst.app (op T) z = x ∧ snd.app (op T) z = y :=
  Types.exists_of_isPullback (h.map ((evaluation _ _).obj (op T))) x y hxy

/-- Two maps into fppf sheaves have an fppf-sheaf pullback. -/
theorem exists_sheaf_isPullback {A B C : FppfSheaf S} (f : A.obj ⟶ C.obj)
    (g : B.obj ⟶ C.obj) :
    ∃ (G : FppfSheaf S) (φ₁ : G.obj ⟶ A.obj) (φ₂ : G.obj ⟶ B.obj), IsPullback φ₁ φ₂ f g :=
  let f' : A ⟶ C := ObjectProperty.homMk f
  let g' : B ⟶ C := ObjectProperty.homMk g
  ⟨Limits.pullback f' g', _, _,
    (IsPullback.of_hasPullback f' g').map (sheafToPresheaf (fppfTopology S) (Type (u + 1)))⟩

/-- A scheme representing the corner of a presheaf pullback gives a represented square. -/
theorem exists_isPullback_of_iso {F A B : Presheaf S} {T M : Over S} {φ₁ : F ⟶ A}
    {φ₂ : F ⟶ (schemeYoneda S).obj T} {f : A ⟶ B} {g : (schemeYoneda S).obj T ⟶ B}
    (hF : IsPullback φ₁ φ₂ f g) (e : (schemeYoneda S).obj M ≅ F) :
    ∃ (snd : M ⟶ T) (fst : (schemeYoneda S).obj M ⟶ A),
      IsPullback fst ((schemeYoneda S).map snd) f g := by
  obtain ⟨snd, hsnd⟩ := (schemeYoneda S).map_surjective (e.hom ≫ φ₂)
  refine ⟨snd, e.hom ≫ φ₁, ?_⟩
  rw [hsnd]
  exact IsPullback.of_iso hF e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simp) (by simp)

/-- A surjective scheme morphism gives a geometrically surjective represented map. -/
theorem isSurjective_map {W T : Over S} (p : W ⟶ T) (hp : Surjective p.left) :
    IsSurjective ((schemeYoneda S).map p) :=
  haveI : (MorphismProperty.inverseImage (@Surjective.{u})
      (Over.forget S)).IsStableUnderBaseChange := isStableUnderBaseChange_inverseImage_forget
  MorphismProperty.relative_map (P := MorphismProperty.inverseImage (@Surjective.{u})
    (Over.forget S)) hp

/-- An open immersion of schemes gives a representable open immersion. -/
theorem isOpenImmersion_map {W T : Over S} (p : W ⟶ T)
    (hp : _root_.AlgebraicGeometry.IsOpenImmersion p.left) :
    IsOpenImmersion ((schemeYoneda S).map p) :=
  haveI : (MorphismProperty.inverseImage (@_root_.AlgebraicGeometry.IsOpenImmersion.{u})
      (Over.forget S)).IsStableUnderBaseChange := isStableUnderBaseChange_inverseImage_forget
  MorphismProperty.relative_map (P := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsOpenImmersion.{u}) (Over.forget S)) hp

/-- The base change of a surjective étale scheme map is étale and surjective. -/
theorem isEtale_isSurjective_of_isPullback {F : Presheaf S} {Z W T : Over S}
    {c : (schemeYoneda S).obj Z ⟶ F} {j : Z ⟶ W} {φ : F ⟶ (schemeYoneda S).obj T}
    {p : W ⟶ T} (h : IsPullback c ((schemeYoneda S).map j) φ ((schemeYoneda S).map p))
    (hp : Etale p.left) (hps : Surjective p.left) : IsEtale c ∧ IsSurjective c :=
  ⟨(MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback h.flip
      (isEtale_map p hp),
    (MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback h.flip
      (isSurjective_map p hps)⟩

/-- A presheaf map into a scheme pulled back along an étale cover to an open immersion is
represented by the image open of the cover. -/
theorem exists_iso_of_isOpenImmersion {F : FppfSheaf S} {Z W T : Over S}
    {c : (schemeYoneda S).obj Z ⟶ F.obj} {j : Z ⟶ W} {φ : F.obj ⟶ (schemeYoneda S).obj T}
    {p : W ⟶ T} (hpb : IsPullback c ((schemeYoneda S).map j) φ ((schemeYoneda S).map p))
    [Etale p.left] [Surjective p.left] [_root_.AlgebraicGeometry.IsOpenImmersion j.left] :
    ∃ M : Over S, Nonempty ((schemeYoneda S).obj M ≅ F.obj) := by
  let O : T.left.Opens :=
    ⟨Set.range (j.left ≫ p.left), (j.left ≫ p.left).isOpenMap.isOpen_range⟩
  let M : Over S := Over.mk (O.ι ≫ T.hom)
  have hO : Set.range (j.left ≫ p.left) ⊆ Set.range O.ι := by
    rw [Scheme.Opens.range_ι]
    exact le_rfl
  let q₀ : Z.left ⟶ O := _root_.AlgebraicGeometry.IsOpenImmersion.lift O.ι _ hO
  have hq₀ : q₀ ≫ O.ι = j.left ≫ p.left := _root_.AlgebraicGeometry.IsOpenImmersion.lift_fac _ _ _
  let q : Z ⟶ M := Over.homMk q₀ (by
    change q₀ ≫ O.ι ≫ T.hom = Z.hom
    rw [reassoc_of% hq₀, Over.w p, Over.w j])
  have hqι : ∀ {T' : Over S} (w : T' ⟶ Z), (w ≫ q).left ≫ O.ι = (w ≫ j ≫ p).left := by
    intro T' w
    simp only [Over.comp_left, Category.assoc]
    exact congrArg (w.left ≫ ·) hq₀
  have : Etale (q₀ ≫ O.ι) := by rw [hq₀]; infer_instance
  have : Etale q.left := Etale.of_comp q₀ O.ι
  have : Surjective q.left := by
    refine ⟨fun x => ?_⟩
    obtain ⟨z, hz⟩ : x.1 ∈ Set.range (j.left ≫ p.left) := x.2
    refine ⟨z, O.ι.isOpenEmbedding.injective ?_⟩
    change (q₀ ≫ O.ι) z = O.ι x
    rw [hq₀, hz]
    rfl
  have hc := isEtale_isSurjective_of_isPullback hpb ‹_› ‹_›
  have hφ : ∀ {T' : Over S} (w : T' ⟶ Z),
      φ.app (op T') (c.app (op T') ⟨w⟩) = ⟨w ≫ j ≫ p⟩ := by
    intro T' w
    have := types_congr_hom (NatTrans.congr_app hpb.w (op T')) ⟨w⟩
    simpa using this
  refine ⟨M, ⟨(exists_iso_of_locallySurjective_of_same_kernel c q
    (isLocallySurjective_of_isEtale c hc.1 hc.2) (isLocallySurjective_map q) ?_).choose⟩⟩
  intro T' w₁ w₂
  constructor
  · intro h
    have h' := congrArg (φ.app (op T')) h
    rw [hφ, hφ] at h'
    have h'' : w₁ ≫ j ≫ p = w₂ ≫ j ≫ p := congrArg ULift.down h'
    ext1
    rw [← cancel_mono O.ι, hqι, hqι, h'']
  · intro h
    have h' : w₁ ≫ j ≫ p = w₂ ≫ j ≫ p := by
      ext1
      rw [← hqι, ← hqι, h]
    obtain ⟨z, hz₁, hz₂⟩ := exists_app_of_isPullback hpb T' (c.app (op T') ⟨w₁⟩) ⟨w₂ ≫ j⟩
      (by rw [hφ, h']; rfl)
    have hz : z.down = w₂ := by
      have hz₂' : z.down ≫ j = w₂ ≫ j := congrArg ULift.down hz₂
      apply Over.OverMorphism.ext
      rw [← cancel_mono j.left, ← Over.comp_left, ← Over.comp_left, hz₂']
    rw [← hz₁, ← hz]
    rfl

/-- A surjective étale map onto an affine scheme is refined by one from an affine scheme. -/
theorem exists_affine_refinement {W T : Over S} (p : W ⟶ T) [Etale p.left] [Surjective p.left]
    [IsAffine T.left] :
    ∃ (W' : Over S) (J : W' ⟶ W), IsAffine W'.left ∧ Etale J.left ∧ Surjective (J ≫ p).left := by
  let 𝒰 := W.left.affineCover
  let G : 𝒰.I₀ → Set T.left := fun x => p.left '' Set.range (𝒰.f x)
  have hG : ∀ x, IsOpen (G x) := fun x =>
    p.left.isOpenMap _ (𝒰.f x).isOpenEmbedding.isOpen_range
  have hcov : Set.univ ⊆ ⋃ x, G x := by
    intro v _
    obtain ⟨w, rfl⟩ := Surjective.surj (f := p.left) v
    exact Set.mem_iUnion.2 ⟨𝒰.idx w, w, 𝒰.covers w, rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover G hG hcov
  let g : t → Scheme.{u} := fun i => 𝒰.X i
  let J₀ : ∐ g ⟶ W.left := Sigma.desc fun i => 𝒰.f i
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
  have hJ : Etale J₀ := IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance
  refine ⟨Over.mk (J₀ ≫ W.hom), Over.homMk J₀, inferInstanceAs (IsAffine (∐ g)), hJ,
    ⟨fun v => ?_⟩⟩
  obtain ⟨i, hi, hv⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ v))
  obtain ⟨w, ⟨y, rfl⟩, rfl⟩ := hv
  refine ⟨Sigma.ι g ⟨i, hi⟩ y, ?_⟩
  change (Sigma.ι g ⟨i, hi⟩ ≫ J₀ ≫ p.left) y = _
  rw [Sigma.ι_comp_desc_assoc]
  rfl

/-- Over affine schemes, a presheaf map into a scheme whose pullback along an étale cover is
represented by affine schemes is itself represented. -/
theorem exists_iso_of_isAffine {F : FppfSheaf S} {Z W T : Over S}
    {c : (schemeYoneda S).obj Z ⟶ F.obj} {j : Z ⟶ W} {φ : F.obj ⟶ (schemeYoneda S).obj T}
    {p : W ⟶ T} (hpb : IsPullback c ((schemeYoneda S).map j) φ ((schemeYoneda S).map p))
    [Etale p.left] [Surjective p.left] [IsAffine Z.left] [IsAffine W.left] [IsAffine T.left] :
    ∃ M : Over S, Nonempty ((schemeYoneda S).obj M ≅ F.obj) := by
  have hc := isEtale_isSurjective_of_isPullback hpb ‹_› ‹_›
  obtain ⟨R, t, s, hk, ht, hs⟩ := exists_kernelPair hc.1
  have h₁ := hk.paste_horiz hpb.flip
  rw [hpb.w, ← Functor.map_comp, ← Functor.map_comp] at h₁
  have h₂ : IsPullback (t.left ≫ j.left) s.left p.left (j.left ≫ p.left) :=
    (isPullback_of_map h₁).map (Over.forget S)
  let E := EtaleEquivalenceRelation.ofKernelPair t s c hk ht hs
  have : IsAffine E.U := ‹IsAffine Z.left›
  have hq := EtaleEquivalenceRelation.hasAffineQuotient_of_isPullback_kernelPair p.left E j.left h₂
  obtain ⟨M, -, e⟩ :=
    EtaleEquivalenceRelation.exists_isAffine_iso_of_hasAffineQuotient hk ht hs hc.1 hc.2 hq
  exact ⟨M, e⟩

/-- Zariski gluing over the target: if the pullback of `φ` to every affine scheme over `T` is
represented, then the fppf sheaf `F` is represented. -/
theorem exists_iso_of_affine_pullbacks {F : FppfSheaf S} {T : Over S}
    (φ : F.obj ⟶ (schemeYoneda S).obj T)
    (H : ∀ (T' : Over S) [IsAffine T'.left] (ι : T' ⟶ T) (G : FppfSheaf S)
      (ψ₁ : G.obj ⟶ F.obj) (ψ₂ : G.obj ⟶ (schemeYoneda S).obj T'),
      IsPullback ψ₁ ψ₂ φ ((schemeYoneda S).map ι) →
        ∃ M : Over S, Nonempty ((schemeYoneda S).obj M ≅ G.obj)) :
    ∃ M : Over S, Nonempty ((schemeYoneda S).obj M ≅ F.obj) := by
  let 𝒰 := T.left.affineCover
  let Tk : 𝒰.I₀ → Over S := fun k => Over.mk (𝒰.f k ≫ T.hom)
  let ι : ∀ k, Tk k ⟶ T := fun k => Over.homMk (𝒰.f k)
  have hG : ∀ k, ∃ (G : FppfSheaf S) (ψ₁ : G.obj ⟶ F.obj)
      (ψ₂ : G.obj ⟶ (schemeYoneda S).obj (Tk k)),
      IsPullback ψ₁ ψ₂ φ ((schemeYoneda S).map (ι k)) := fun k =>
    exists_sheaf_isPullback (B := (schemeSheaf S).obj (Tk k)) (C := (schemeSheaf S).obj T) φ
      ((schemeYoneda S).map (ι k))
  choose G ψ₁ ψ₂ hψ using hG
  have hM : ∀ k, ∃ M : Over S, Nonempty ((schemeYoneda S).obj M ≅ (G k).obj) := fun k =>
    have : IsAffine (Tk k).left := inferInstanceAs (IsAffine (𝒰.X k))
    H (Tk k) (ι k) (G k) (ψ₁ k) (ψ₂ k) (hψ k)
  choose M e using hM
  let chart : ∀ k, (schemeYoneda S).obj (M k) ⟶ F.obj := fun k => (e k).some.hom ≫ ψ₁ k
  have hopen : ∀ k, IsOpenImmersion (chart k) := fun k =>
    IsOpenImmersion.iso_comp _ ((MorphismProperty.relative_isStableUnderBaseChange _).of_isPullback
      (hψ k).flip (isOpenImmersion_map (ι k) (inferInstanceAs
        (_root_.AlgebraicGeometry.IsOpenImmersion (𝒰.f k)))))
  have hcov : Sieve.ofArrows Tk ι ∈ fppfTopology S T := by
    rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    exact (Precoverage.toGrothendieck_mono
      Scheme.zariskiPrecoverage_le_fppfPrecoverage) _ 𝒰.mem_grothendieckTopology
  have hsurj : CategoryTheory.Presheaf.IsLocallySurjective (fppfTopology S)
      (Sigma.desc chart) := by
    constructor
    intro T' x
    refine (fppfTopology S).superset_covering ?_
      ((fppfTopology S).pullback_stable (φ.app (op T') x).down hcov)
    intro T'' u hu
    obtain ⟨k, α, hα⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hu
    have hx : φ.app (op T'') (F.obj.map u.op x) =
        ((schemeYoneda S).map (ι k)).app (op T'') ⟨α⟩ := by
      rw [NatTrans.naturality_apply]
      exact congrArg ULift.up hα
    obtain ⟨y, hy₁, -⟩ := exists_app_of_isPullback (hψ k) T'' _ _ hx
    refine ⟨(Sigma.ι (fun k => (schemeYoneda S).obj (M k)) k).app (op T'')
      ((e k).some.inv.app (op T'') y), ?_⟩
    have h₁ := congrArg (fun η => η.app (op T'') ((e k).some.inv.app (op T'') y))
      (Sigma.ι_comp_desc chart k)
    refine h₁.trans ?_
    simp only [chart, NatTrans.comp_app, types_comp_apply]
    rw [← hy₁]
    congr 1
    exact congrArg (fun η => η.app (op T'') y) (e k).some.inv_hom_id
  exact openChartGluing S F 𝒰.I₀ M chart hopen hsurj

section Local

variable {X Y : AlgebraicSpace S} {f : X ⟶ Y} {U V : Over S}
  {a : (schemeYoneda S).obj U ⟶ X.presheaf} {b : (schemeYoneda S).obj V ⟶ Y.presheaf}
  {q : U ⟶ V}

/-- Over a scheme `W` mapping to both the test and the atlas, the pullback of the test
is the scheme pullback of `q`. -/
theorem exists_local_isPullback (hsq : IsPullback a ((schemeYoneda S).map q) (hom f) b)
    {T : Over S} {g : (schemeYoneda S).obj T ⟶ Y.presheaf}
    {F : Presheaf S} {φ₁ : F ⟶ X.presheaf} {φ₂ : F ⟶ (schemeYoneda S).obj T}
    (hF : IsPullback φ₁ φ₂ (hom f) g) {W : Over S} (p : W ⟶ T) (w : W ⟶ V)
    (hw : (schemeYoneda S).map w ≫ b = (schemeYoneda S).map p ≫ g) :
    ∃ c : (schemeYoneda S).obj (Limits.pullback q w) ⟶ F,
      IsPullback c ((schemeYoneda S).map (pullback.snd q w)) φ₂ ((schemeYoneda S).map p) := by
  have outer := ((IsPullback.of_hasPullback q w).map (schemeYoneda S)).paste_horiz hsq
  rw [hw] at outer
  have hc : ((schemeYoneda S).map (pullback.fst q w) ≫ a) ≫ hom f =
      (schemeYoneda S).map (pullback.snd q w) ≫ (schemeYoneda S).map p ≫ g := by
    rw [← hw, Category.assoc, hsq.w, ← Functor.map_comp_assoc, pullback.condition,
      Functor.map_comp_assoc]
  refine ⟨hF.lift _ _ hc, IsPullback.of_right ?_ (hF.lift_snd _ _ hc) hF⟩
  rwa [hF.lift_fst]


/-- For an affine scheme mapping to `Y`, the pullback of `hom f` is represented when `q` is
an affine morphism. -/
theorem exists_iso_of_isAffine_test (hsq : IsPullback a ((schemeYoneda S).map q) (hom f) b)
    (hbe : IsEtale b) (hbs : IsSurjective b) [IsAffineHom q.left]
    {T : Over S} [IsAffine T.left] {g : (schemeYoneda S).obj T ⟶ Y.presheaf}
    {F : FppfSheaf S} {φ₁ : F.obj ⟶ X.presheaf} {φ₂ : F.obj ⟶ (schemeYoneda S).obj T}
    (hF : IsPullback φ₁ φ₂ (hom f) g) :
    ∃ M : Over S, Nonempty ((schemeYoneda S).obj M ≅ F.obj) := by
  let hr := hbe.representable
  have hP := hr.isPullback g
  obtain ⟨w, hw⟩ := (schemeYoneda S).map_surjective (hr.fst g)
  rw [← hw] at hP
  have : Etale (hr.snd g).left := hbe.projection g _ _ hP
  have : Surjective (hr.snd g).left := hbs.projection g _ _ hP
  obtain ⟨W', J, hW', hJ, hJs⟩ := exists_affine_refinement (hr.snd g)
  have : Etale (J ≫ hr.snd g).left := by rw [Over.comp_left]; infer_instance
  obtain ⟨c, hc⟩ := exists_local_isPullback hsq hF (J ≫ hr.snd g) (J ≫ w)
    (by simp only [Functor.map_comp, Category.assoc, hP.w])
  have hpb := (IsPullback.of_hasPullback q (J ≫ w)).map (Over.forget S)
  have : IsAffineHom (pullback.snd q (J ≫ w)).left :=
    MorphismProperty.of_isPullback (P := @IsAffineHom) hpb ‹_›
  have : IsAffine (Limits.pullback q (J ≫ w)).left :=
    isAffine_of_isAffineHom (pullback.snd q (J ≫ w)).left
  exact exists_iso_of_isAffine hc

/-- For an affine morphism `q`, every pullback of `hom f` along a scheme point is
represented. -/
theorem exists_iso_of_isAffineHom (hsq : IsPullback a ((schemeYoneda S).map q) (hom f) b)
    (hbe : IsEtale b) (hbs : IsSurjective b) [IsAffineHom q.left]
    {T : Over S} {g : (schemeYoneda S).obj T ⟶ Y.presheaf}
    {F : FppfSheaf S} {φ₁ : F.obj ⟶ X.presheaf} {φ₂ : F.obj ⟶ (schemeYoneda S).obj T}
    (hF : IsPullback φ₁ φ₂ (hom f) g) :
    ∃ M : Over S, Nonempty ((schemeYoneda S).obj M ≅ F.obj) :=
  exists_iso_of_affine_pullbacks φ₂ fun _ _ _ _ _ _ hψ =>
    exists_iso_of_isAffine_test hsq hbe hbs (hψ.flip.paste_vert hF.flip).flip

/-- For an open immersion `q`, every pullback of `hom f` along a scheme point is
represented. -/
theorem exists_iso_of_isOpenImmersion_test
    (hsq : IsPullback a ((schemeYoneda S).map q) (hom f) b)
    (hbe : IsEtale b) (hbs : IsSurjective b) [_root_.AlgebraicGeometry.IsOpenImmersion q.left]
    {T : Over S} {g : (schemeYoneda S).obj T ⟶ Y.presheaf}
    {F : FppfSheaf S} {φ₁ : F.obj ⟶ X.presheaf} {φ₂ : F.obj ⟶ (schemeYoneda S).obj T}
    (hF : IsPullback φ₁ φ₂ (hom f) g) :
    ∃ M : Over S, Nonempty ((schemeYoneda S).obj M ≅ F.obj) := by
  let hr := hbe.representable
  have hP := hr.isPullback g
  obtain ⟨w, hw⟩ := (schemeYoneda S).map_surjective (hr.fst g)
  rw [← hw] at hP
  have : Etale (hr.snd g).left := hbe.projection g _ _ hP
  have : Surjective (hr.snd g).left := hbs.projection g _ _ hP
  obtain ⟨c, hc⟩ := exists_local_isPullback hsq hF (hr.snd g) w hP.w
  have hpb := (IsPullback.of_hasPullback q w).map (Over.forget S)
  have : _root_.AlgebraicGeometry.IsOpenImmersion (pullback.snd q w).left :=
    MorphismProperty.of_isPullback (P := @_root_.AlgebraicGeometry.IsOpenImmersion) hpb ‹_›
  exact exists_iso_of_isOpenImmersion hc

end Local

/-- A map of algebraic spaces is representable once each fppf-sheaf pullback along a scheme
point is represented. -/
theorem isRepresentableMorphism_of_pullbacks {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    (H : ∀ (T : Over S) (g : (schemeYoneda S).obj T ⟶ Y.presheaf) (F : FppfSheaf S)
      (φ₁ : F.obj ⟶ X.presheaf) (φ₂ : F.obj ⟶ (schemeYoneda S).obj T),
      IsPullback φ₁ φ₂ (hom f) g → ∃ M : Over S, Nonempty ((schemeYoneda S).obj M ≅ F.obj)) :
    IsRepresentableMorphism (hom f) := by
  intro T g
  obtain ⟨F, φ₁, φ₂, hF⟩ :=
    exists_sheaf_isPullback (A := X.toSheaf) (B := (schemeSheaf S).obj T) (C := Y.toSheaf)
      (hom f) g
  obtain ⟨M, ⟨e⟩⟩ := H T g F φ₁ φ₂ hF
  obtain ⟨snd, fst, hsq⟩ := exists_isPullback_of_iso hF e
  exact ⟨M, snd, fst, hsq⟩

end AtlasEffectivity

end Langlands.AlgebraicGeometry.AlgebraicSpace
