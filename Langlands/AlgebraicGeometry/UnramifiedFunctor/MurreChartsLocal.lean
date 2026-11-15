import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalSteps

/-! # Local properties of elements of a functor, for Murre's charts

Tools for the construction of the charts in `MurreNoetherianChartsStatement`:

* transfer of infinitesimal étaleness (`InfinitesimallyEtaleAt`) to and from open subschemes
  and along morphisms through which local artinian points factor uniquely;
* infinitesimal étaleness of open immersions into a scheme representing the base change of
  `F` along a monomorphism `g : S' ⟶ S` (for instance `Spec 𝒪_{S,s} ⟶ S`);
* the criterion "two morphisms into a scheme with open diagonal agree when they agree at
  every point", and its version over a local scheme. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace Charts

section Points

/-- All points of the spectrum of a local artinian ring are equal. -/
lemma eq_of_isArtinianRing {L : Type u} [CommRing L] [IsLocalRing L] [IsArtinianRing L]
    (x y : Spec (CommRingCat.of L)) : x = y := by
  have h : ∀ z : Spec (CommRingCat.of L), z.asIdeal = IsLocalRing.maximalIdeal L := fun z => by
    have := z.isPrime
    exact IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_of_isPrime z.asIdeal)
  exact PrimeSpectrum.ext ((h x).trans (h y).symm)

lemma ne_top_of_isNilpotent {A : Type u} [CommRing A] [Nontrivial A] {J : Ideal A}
    (hJ : IsNilpotent J) : J ≠ ⊤ := by
  obtain ⟨n, hn⟩ := hJ
  intro h
  rw [h, Ideal.top_pow] at hn
  exact top_ne_bot hn

lemma isLocalRing_quotient {A : Type u} [CommRing A] [IsLocalRing A] {J : Ideal A}
    (hJ : IsNilpotent J) : IsLocalRing (A ⧸ J) :=
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 (ne_top_of_isNilpotent hJ)
  IsLocalRing.of_surjective' (Ideal.Quotient.mk J) Ideal.Quotient.mk_surjective

end Points

variable {S : Scheme.{u}} {F : (Over S)ᵒᵖ ⥤ Type v}

section Etale

/-- Infinitesimal étaleness descends along a morphism `ρ : V ⟶ U` through which every
morphism from the spectrum of a local artinian ring to `U` with image `y` factors uniquely. -/
theorem infinitesimallyEtaleAt_of_factor {U V : Over S} (ρ : V ⟶ U) (ξ : F.obj (op U))
    (y : U.left)
    (hfac : ∀ (L : Type u) [CommRing L] [IsLocalRing L] [IsArtinianRing L]
      (w : Spec (CommRingCat.of L) ⟶ U.left), (∀ x, w x = y) →
        ∃! w' : Spec (CommRingCat.of L) ⟶ V.left, w' ≫ ρ.left = w)
    (het : ∀ y', ρ.left y' = y → InfinitesimallyEtaleAt F (F.map ρ.op ξ) y') :
    InfinitesimallyEtaleAt F ξ y := by
  intro A _ _ _ f J hJ u₀ hu₀ v hv
  have := isLocalRing_quotient hJ
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 (ne_top_of_isNilpotent hJ)
  obtain ⟨w₀, hw₀, huniq₀⟩ := hfac (A ⧸ J) u₀.left hu₀
  let u₀' : algebraOver f (A ⧸ J) ⟶ V := Over.homMk w₀ (by
    rw [← Over.w ρ, ← Category.assoc, hw₀, Over.w u₀])
  have hu₀' : u₀' ≫ ρ = u₀ := by
    ext1
    exact hw₀
  obtain ⟨x₀⟩ : Nonempty (Spec (CommRingCat.of (A ⧸ J))) := inferInstance
  have hy' : ρ.left (w₀ x₀) = y := by rw [← Scheme.Hom.comp_apply, hw₀, hu₀]
  obtain ⟨u', ⟨hu'₁, hu'₂⟩, huniq⟩ := het (w₀ x₀) hy' A f J hJ u₀'
    (fun x => by rw [eq_of_isArtinianRing x x₀]; rfl) v (by
      rw [← Functor.map_comp_apply, ← op_comp, hu₀', hv])
  refine ⟨u' ≫ ρ, ⟨by rw [← Category.assoc, hu'₁, hu₀'], by
    rw [op_comp, Functor.map_comp_apply, hu'₂]⟩, ?_⟩
  rintro u₁ ⟨hu₁₁, hu₁₂⟩
  have hu₁y : ∀ x, u₁.left x = y := by
    intro x
    rw [eq_of_isArtinianRing x ((algebraOverBase f (A ⧸ J)).left x₀), ← Scheme.Hom.comp_apply,
      ← Over.comp_left, hu₁₁, hu₀]
  obtain ⟨w₁, hw₁, -⟩ := hfac A u₁.left hu₁y
  let u₁' : Over.mk f ⟶ V := Over.homMk w₁ (by
    rw [← Over.w ρ, ← Category.assoc, hw₁]
    exact Over.w u₁)
  have hu₁' : u₁' ≫ ρ = u₁ := by
    ext1
    exact hw₁
  have : u₁' = u' := by
    refine huniq u₁' ⟨?_, ?_⟩
    · ext1
      refine huniq₀ _ ?_
      show (_ ≫ _) ≫ ρ.left = u₀.left
      rw [Category.assoc, show u₁'.left ≫ ρ.left = u₁.left from hw₁, ← Over.comp_left, hu₁₁]
    · rw [← Functor.map_comp_apply, ← op_comp, hu₁', hu₁₂]
  rw [← hu₁', this]

/-- Infinitesimal étaleness restricts to open subschemes. -/
theorem infinitesimallyEtaleAt_restrict {U V : Over S} (ι : V ⟶ U) [IsOpenImmersion ι.left]
    {ξ : F.obj (op U)} {y : V.left} (h : InfinitesimallyEtaleAt F ξ (ι.left y)) :
    InfinitesimallyEtaleAt F (F.map ι.op ξ) y := by
  intro A _ _ _ f J hJ u₀ hu₀ v hv
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 (ne_top_of_isNilpotent hJ)
  obtain ⟨x₀⟩ : Nonempty (Spec (CommRingCat.of (A ⧸ J))) := inferInstance
  obtain ⟨u, ⟨hu₁, hu₂⟩, huniq⟩ := h A f J hJ (u₀ ≫ ι)
    (fun x => by rw [Over.comp_left, Scheme.Hom.comp_apply, hu₀]) v
    (by rw [op_comp, Functor.map_comp_apply, hv])
  have hrange : Set.range u.left ⊆ Set.range ι.left := by
    rintro _ ⟨x, rfl⟩
    rw [eq_of_isArtinianRing x ((algebraOverBase f (A ⧸ J)).left x₀), ← Scheme.Hom.comp_apply,
      ← Over.comp_left, hu₁, Over.comp_left, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let l := IsOpenImmersion.lift ι.left u.left hrange
  have hl : l ≫ ι.left = u.left := IsOpenImmersion.lift_fac _ _ _
  let u' : Over.mk f ⟶ V := Over.homMk l (by
    rw [← Over.w ι, ← Category.assoc, hl]
    exact Over.w u)
  have hu' : u' ≫ ι = u := by
    ext1
    exact hl
  refine ⟨u', ⟨?_, ?_⟩, ?_⟩
  · ext1
    rw [← cancel_mono ι.left]
    have := congrArg (fun k => k.left) hu₁
    simp only [Over.comp_left] at this ⊢
    rw [Category.assoc, show u'.left = l from rfl, hl, this]
  · rw [← Functor.map_comp_apply, ← op_comp, hu', hu₂]
  · rintro u₁ ⟨h₁, h₂⟩
    have : u₁ ≫ ι = u := huniq _ ⟨by rw [← Category.assoc, h₁], by
      rw [op_comp, Functor.map_comp_apply, h₂]⟩
    ext1
    rw [← cancel_mono ι.left, ← Over.comp_left, this]
    exact hl.symm

/-- Monomorphic elements restrict along monomorphisms. -/
lemma isMonoElement_restrict {U V : Over S} (ι : V ⟶ U) [Mono ι.left] {ξ : F.obj (op U)}
    (h : IsMonoElement F ξ) : IsMonoElement F (F.map ι.op ξ) := by
  intro T h₁ h₂ heq
  have : h₁ ≫ ι = h₂ ≫ ι := h _ _ (by
    rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply, heq])
  ext1
  rw [← cancel_mono ι.left, ← Over.comp_left, ← Over.comp_left, this]

end Etale

section Rep

variable {S' : Scheme.{u}} (g : S' ⟶ S) {Y' : Over S'}
  (e : (baseChange g F).RepresentableBy Y')

/-- An object of `Over S` whose structure morphism factors as `t ≫ g`, as the image of the
object `t` of `Over S'`. -/
def liftIso (T : Over S) (t : T.left ⟶ S') (ht : t ≫ g = T.hom) :
    T ≅ (Over.map g).obj (Over.mk t) :=
  Over.isoMk (Iso.refl _) (by simp [ht])

/-- For `T` over `S` with structure morphism `t ≫ g`, the bijection between `S'`-morphisms
`t ⟶ Y'` and `F(T)`. -/
def elemEquiv (T : Over S) (t : T.left ⟶ S') (ht : t ≫ g = T.hom) :
    (Over.mk t ⟶ Y') ≃ F.obj (op T) :=
  e.homEquiv.trans (F.mapIso (liftIso g T t ht).op).toEquiv

lemma elemEquiv_apply (T : Over S) (t : T.left ⟶ S') (ht : t ≫ g = T.hom)
    (a : Over.mk t ⟶ Y') :
    elemEquiv g e T t ht a = F.map (liftIso g T t ht).hom.op (e.homEquiv a) := rfl

lemma lift_comp [Mono g] {T₁ T₂ : Over S} (h : T₁ ⟶ T₂) (t₁ : T₁.left ⟶ S')
    (t₂ : T₂.left ⟶ S') (ht₁ : t₁ ≫ g = T₁.hom) (ht₂ : t₂ ≫ g = T₂.hom) :
    h.left ≫ t₂ = t₁ := by
  rw [← cancel_mono g, Category.assoc, ht₂, Over.w h, ht₁]

lemma elemEquiv_naturality [Mono g] {T₁ T₂ : Over S} (h : T₁ ⟶ T₂) (t₁ : T₁.left ⟶ S')
    (t₂ : T₂.left ⟶ S') (ht₁ : t₁ ≫ g = T₁.hom) (ht₂ : t₂ ≫ g = T₂.hom)
    (a : Over.mk t₂ ⟶ Y') :
    F.map h.op (elemEquiv g e T₂ t₂ ht₂ a) =
      elemEquiv g e T₁ t₁ ht₁ ((Over.homMk h.left (lift_comp g h t₁ t₂ ht₁ ht₂) :
        Over.mk t₁ ⟶ Over.mk t₂) ≫ a) := by
  have hcomm : h ≫ (liftIso g T₂ t₂ ht₂).hom = (liftIso g T₁ t₁ ht₁).hom ≫
      (Over.map g).map (Over.homMk h.left (lift_comp g h t₁ t₂ ht₁ ht₂) :
        Over.mk t₁ ⟶ Over.mk t₂) := by
    ext1
    simp [liftIso]
  rw [elemEquiv_apply, elemEquiv_apply, e.homEquiv_comp]
  change (F.map (liftIso g T₂ t₂ ht₂).hom.op ≫ F.map h.op) (e.homEquiv a) =
    (F.map ((Over.map g).map (Over.homMk h.left (lift_comp g h t₁ t₂ ht₁ ht₂) :
        Over.mk t₁ ⟶ Over.mk t₂)).op ≫ F.map (liftIso g T₁ t₁ ht₁).hom.op) (e.homEquiv a)
  rw [← F.map_comp, ← F.map_comp, ← op_comp, ← op_comp, hcomm]

/-- Let `g : S' ⟶ S` be a monomorphism through which every morphism from the spectrum of a
local artinian ring to `S` with image in the image of `g` factors. If the base change of `F`
along `g` is represented by `Y'`, then for every open immersion `j : V ⟶ Y'` over `S'` the
corresponding element of `F(V)` is infinitesimally étale at every point. -/
theorem infinitesimallyEtaleAt_elemEquiv [Mono g]
    (hg : ∀ (L : Type u) [CommRing L] [IsLocalRing L] [IsArtinianRing L]
      (f : Spec (CommRingCat.of L) ⟶ S), (∀ x, f x ∈ Set.range g) →
        ∃ f' : Spec (CommRingCat.of L) ⟶ S', f' ≫ g = f)
    {V : Over S} (w : V.left ⟶ S') (hw : w ≫ g = V.hom) (j : Over.mk w ⟶ Y')
    [IsOpenImmersion j.left] (y : V.left) :
    InfinitesimallyEtaleAt F (elemEquiv g e V w hw j) y := by
  intro A _ _ _ f J hJ u₀ _ v hv
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.2 (ne_top_of_isNilpotent hJ)
  obtain ⟨x₀⟩ : Nonempty (Spec (CommRingCat.of (A ⧸ J))) := inferInstance
  set base := algebraOverBase f (A ⧸ J)
  have hbase : base.left ≫ f = u₀.left ≫ V.hom := by
    rw [Over.w u₀]
    exact Over.w base
  have hpts : ∀ x, f x ∈ Set.range g := fun x => by
    rw [eq_of_isArtinianRing x (base.left x₀), ← Scheme.Hom.comp_apply, hbase, ← hw,
      Scheme.Hom.comp_apply, Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  obtain ⟨f', hf'⟩ := hg A f hpts
  have ht₀ : (base.left ≫ f') ≫ g = (algebraOver f (A ⧸ J)).hom := by
    rw [Category.assoc, hf']
    exact Over.w base
  let E := elemEquiv g e (Over.mk f) f' hf'
  let E₀ := elemEquiv g e (algebraOver f (A ⧸ J)) (base.left ≫ f') ht₀
  rw [← E.apply_symm_apply v, elemEquiv_naturality g e u₀ (base.left ≫ f') w ht₀ hw j,
    elemEquiv_naturality g e base (base.left ≫ f') f' ht₀ hf'] at hv
  have hkey : u₀.left ≫ j.left = base.left ≫ (E.symm v).left := by
    have := congrArg (fun k => k.left) (E₀.injective hv)
    simpa using this
  have hrange : Set.range (E.symm v).left ⊆ Set.range j.left := by
    rintro _ ⟨x, rfl⟩
    rw [eq_of_isArtinianRing x (base.left x₀), ← Scheme.Hom.comp_apply, ← hkey,
      Scheme.Hom.comp_apply]
    exact ⟨_, rfl⟩
  let l := IsOpenImmersion.lift j.left (E.symm v).left hrange
  have hl : l ≫ j.left = (E.symm v).left := IsOpenImmersion.lift_fac _ _ _
  have hlw : l ≫ V.hom = f := by
    rw [← hw, ← Category.assoc]
    have h1 : l ≫ w = f' := by
      have h2 := Over.w j
      have h3 := Over.w (E.symm v)
      simp only [Over.mk_hom] at h2 h3
      rw [← h2, ← Category.assoc, hl, h3]
    rw [h1, hf']
  let u : Over.mk f ⟶ V := Over.homMk l hlw
  refine ⟨u, ⟨?_, ?_⟩, ?_⟩
  · ext1
    rw [← cancel_mono j.left, Over.comp_left, Category.assoc]
    simp only [u, Over.homMk_left, hl, hkey]
  · rw [elemEquiv_naturality g e u f' w hf' hw j]
    convert E.apply_symm_apply v using 2
    ext1
    simp [u, hl]
  · rintro u₁ ⟨-, h₂⟩
    rw [← E.apply_symm_apply v, elemEquiv_naturality g e u₁ f' w hf' hw j] at h₂
    have h₃ := congrArg (fun k => k.left) (E.injective h₂)
    simp only [Over.comp_left, Over.homMk_left] at h₃
    ext1
    rw [← cancel_mono j.left, h₃]
    simp [u, hl]

end Rep

section Diagonal

variable {S' U Z : Scheme.{u}} (q : U ⟶ S') (h₁ h₂ : Z ⟶ U) (w : h₁ ≫ q = h₂ ≫ q)

/-- Two morphisms into `U` whose pair maps every point into the image of the diagonal of
`U ⟶ S'`, an open immersion, are equal. -/
lemma eq_of_forall_mem_range_diagonal [IsOpenImmersion (pullback.diagonal q)]
    (H : ∀ z, pullback.lift h₁ h₂ w z ∈ Set.range (pullback.diagonal q)) : h₁ = h₂ := by
  have hsub : Set.range (pullback.lift h₁ h₂ w) ⊆ Set.range (pullback.diagonal q) := by
    rintro _ ⟨z, rfl⟩
    exact H z
  have hl := IsOpenImmersion.lift_fac (pullback.diagonal q) (pullback.lift h₁ h₂ w) hsub
  have e₁ := congrArg (· ≫ pullback.fst q q) hl
  have e₂ := congrArg (· ≫ pullback.snd q q) hl
  simp only [Category.assoc, pullback.diagonal_fst, pullback.diagonal_snd, Category.comp_id,
    pullback.lift_fst, pullback.lift_snd] at e₁ e₂
  exact e₁.symm.trans e₂

/-- If `h₁` and `h₂` agree after composing with `k : W ⟶ Z`, the pair `(h₁, h₂)` maps the
image of `k` into the image of the diagonal. -/
lemma lift_mem_range_diagonal {W : Scheme.{u}} (k : W ⟶ Z) (hk : k ≫ h₁ = k ≫ h₂) (x : W) :
    pullback.lift h₁ h₂ w (k x) ∈ Set.range (pullback.diagonal q) := by
  refine ⟨(k ≫ h₁) x, ?_⟩
  have : (k ≫ h₁) ≫ pullback.diagonal q = k ≫ pullback.lift h₁ h₂ w := by
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, pullback.diagonal_fst, Category.comp_id,
        Category.assoc, pullback.lift_fst]
    · rw [Category.assoc, Category.assoc, pullback.diagonal_snd, Category.comp_id,
        Category.assoc, pullback.lift_snd, hk]
  rw [← Scheme.Hom.comp_apply, this, Scheme.Hom.comp_apply]

lemma isOpen_preimage_range_diagonal [IsOpenImmersion (pullback.diagonal q)] :
    IsOpen ((pullback.lift h₁ h₂ w) ⁻¹' Set.range (pullback.diagonal q)) :=
  (pullback.lift h₁ h₂ w).continuous.isOpen_preimage _ (pullback.diagonal q).isOpenEmbedding.isOpen_range

/-- Two morphisms from the spectrum of a local ring into `U`, whose diagonal over `S'` is an
open immersion, are equal if they agree after composing with a morphism hitting the closed
point. -/
lemma eq_of_isLocalRing [IsOpenImmersion (pullback.diagonal q)] {L : CommRingCat.{u}}
    [IsLocalRing L] (h₁ h₂ : Spec L ⟶ U) (w : h₁ ≫ q = h₂ ≫ q) {W : Scheme.{u}}
    (k : W ⟶ Spec L) (hk : k ≫ h₁ = k ≫ h₂) (x : W) (hx : k x = IsLocalRing.closedPoint L) :
    h₁ = h₂ := by
  apply eq_of_forall_mem_range_diagonal q h₁ h₂ w
  intro z
  have hc : IsLocalRing.closedPoint L ∈
      (pullback.lift h₁ h₂ w) ⁻¹' Set.range (pullback.diagonal q) :=
    hx ▸ lift_mem_range_diagonal q h₁ h₂ w k hk x
  exact (IsLocalRing.specializes_closedPoint z).mem_open
    (isOpen_preimage_range_diagonal q h₁ h₂ w) hc

end Diagonal

section Stalk

instance mono_specMap_of_epi {R R' : CommRingCat.{u}} (φ : R ⟶ R') [Epi φ] :
    Mono (Spec.map φ) :=
  inferInstanceAs (Mono (Scheme.Spec.map φ.op))

instance mono_fromSpecStalk (R : CommRingCat.{u}) (s : Spec R) :
    Mono ((Spec R).fromSpecStalk s) := by
  rw [Spec.fromSpecStalk_eq']
  have := s.isPrime
  let _ : Algebra R ((Spec R).presheaf.stalk s) := StructureSheaf.stalkAlgebra R s
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk s) s.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R s
  have : Epi (StructureSheaf.toStalk R s) :=
    IsLocalization.epi s.asIdeal.primeCompl ((Spec R).presheaf.stalk s)
  exact mono_specMap_of_epi _

/-- A morphism from the spectrum of a local ring to `X`, mapping the closed point to a
generization of `s`, factors through `Spec 𝒪_{X,s} ⟶ X`. -/
lemma exists_comp_fromSpecStalk {X : Scheme.{u}} (s : X) {L : CommRingCat.{u}} [IsLocalRing L]
    (f : Spec L ⟶ X) (hf : f (IsLocalRing.closedPoint L) ⤳ s) :
    ∃ f' : Spec L ⟶ Spec (X.presheaf.stalk s), f' ≫ X.fromSpecStalk s = f :=
  ⟨Spec.map (Scheme.stalkClosedPointTo f) ≫ Spec.map (X.presheaf.stalkSpecializes hf), by
    rw [Category.assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]⟩

/-- The factorization hypothesis of `infinitesimallyEtaleAt_elemEquiv` for
`Spec 𝒪_{X,s} ⟶ X`. -/
lemma fromSpecStalk_factor {X : Scheme.{u}} (s : X) (L : Type u) [CommRing L] [IsLocalRing L]
    [IsArtinianRing L] (f : Spec (CommRingCat.of L) ⟶ X)
    (hf : ∀ x, f x ∈ Set.range (X.fromSpecStalk s)) :
    ∃ f' : Spec (CommRingCat.of L) ⟶ Spec (X.presheaf.stalk s), f' ≫ X.fromSpecStalk s = f := by
  have h := hf (IsLocalRing.closedPoint (CommRingCat.of L))
  rw [Scheme.range_fromSpecStalk] at h
  exact exists_comp_fromSpecStalk s f h

end Stalk

end Charts

end Langlands.AlgebraicGeometry.UnramifiedFunctor
