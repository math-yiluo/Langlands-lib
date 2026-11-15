import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalToGlobalSteps
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreBaseChange
import Mathlib.AlgebraicGeometry.ValuativeCriterion
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-! # Murre's Proposition 2 from its two steps

This module proves `MurreLocalToGlobalStatement` from `MurreChartGluingStatement` (Murre's
Lemma 3) and `MurreNoetherianChartsStatement` (the inductive step of Murre's proof). -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

namespace LocalToGlobal

variable {S : Scheme.{u}}

section Basic

/-- Representability by a separated, locally of finite type, formally unramified scheme is
invariant under isomorphism of presheaves. -/
lemma unramifiedRepresentable_of_iso {F G : (Over S)ᵒᵖ ⥤ Type v} (e : F ≅ G)
    (h : UnramifiedRepresentable F) : UnramifiedRepresentable G := by
  obtain ⟨Y, q, ⟨r⟩, h₁, h₂, h₃⟩ := h
  exact ⟨Y, q, ⟨r.ofIso e⟩, h₁, h₂, h₃⟩

/-- Base change along a composite is the iterated base change. -/
def baseChangeCompIso {S' S'' : Scheme.{u}} (g : S'' ⟶ S') (h : S' ⟶ S)
    (F : (Over S)ᵒᵖ ⥤ Type v) :
    baseChange g (baseChange h F) ≅ baseChange (g ≫ h) F :=
  Functor.isoWhiskerRight (NatIso.op (Over.mapComp g h)) F

/-- The base change of a presheaf represented by `q : Y ⟶ S` along `g : S' ⟶ S` is
represented by the pullback of `q` along `g`. -/
def representableByBaseChange {F : (Over S)ᵒᵖ ⥤ Type v} {Y : Scheme.{u}} {q : Y ⟶ S}
    (e : F.RepresentableBy (Over.mk q)) {S' : Scheme.{u}} (g : S' ⟶ S) :
    (baseChange g F).RepresentableBy ((Over.pullback g).obj (Over.mk q)) where
  homEquiv {T} := ((Over.mapPullbackAdj g).homEquiv T (Over.mk q)).symm.trans e.homEquiv
  homEquiv_comp {T T'} f k := by
    show e.homEquiv ((Over.mapPullbackAdj g).homEquiv _ _ |>.symm (f ≫ k)) =
      F.map ((Over.map g).map f).op (e.homEquiv _)
    rw [Adjunction.homEquiv_naturality_left_symm, e.homEquiv_comp]

/-- Representability by a separated, locally of finite type, formally unramified scheme is
stable under base change. -/
lemma unramifiedRepresentable_baseChange {F : (Over S)ᵒᵖ ⥤ Type v}
    (h : UnramifiedRepresentable F) {S' : Scheme.{u}} (g : S' ⟶ S) :
    UnramifiedRepresentable (baseChange g F) := by
  obtain ⟨Y, q, ⟨r⟩, h₁, h₂, h₃⟩ := h
  exact ⟨_, pullback.snd q g, ⟨representableByBaseChange r g⟩, inferInstance, inferInstance,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback q g) h₃⟩

/-- The hypothesis of Proposition 2 on the local schemes is stable under base change. -/
lemma local_baseChange {F : (Over S)ᵒᵖ ⥤ Type v}
    (hloc : ∀ s : S, UnramifiedRepresentable (baseChange (S.fromSpecStalk s) F))
    {S' : Scheme.{u}} (g : S' ⟶ S) (s' : S') :
    UnramifiedRepresentable (baseChange (S'.fromSpecStalk s') (baseChange g F)) := by
  apply unramifiedRepresentable_of_iso (baseChangeCompIso _ _ F).symm
  rw [← Scheme.SpecMap_stalkMap_fromSpecStalk g]
  exact unramifiedRepresentable_of_iso (baseChangeCompIso _ _ F)
    (unramifiedRepresentable_baseChange (hloc (g s')) _)

end Basic


section Charts

variable {F : (Over S)ᵒᵖ ⥤ Type v}

/-- The universal element of a representable presheaf is a monomorphism. -/
lemma isMonoElement_of_representableBy {Y : Over S} (e : F.RepresentableBy Y) :
    IsMonoElement F (e.homEquiv (𝟙 Y)) := by
  intro T h₁ h₂ h
  rw [← e.homEquiv_comp, ← e.homEquiv_comp] at h
  simpa using e.homEquiv.injective h

/-- The universal element of a representable presheaf is infinitesimally étale at every
point. -/
lemma infinitesimallyEtaleAt_of_representableBy {Y : Over S} (e : F.RepresentableBy Y)
    (y : Y.left) : InfinitesimallyEtaleAt F (e.homEquiv (𝟙 Y)) y := by
  intro A _ _ _ f J _ u₀ _ v hv
  refine ⟨e.homEquiv.symm v, ⟨?_, ?_⟩, ?_⟩
  · apply e.homEquiv.injective
    rw [e.homEquiv_comp, Equiv.apply_symm_apply, ← hv, ← e.homEquiv_comp, Category.comp_id]
  · rw [← e.homEquiv_comp, Category.comp_id, Equiv.apply_symm_apply]
  · rintro u ⟨-, hu⟩
    rw [← hu, ← e.homEquiv_comp, Category.comp_id, Equiv.symm_apply_apply]

variable {S' : Scheme.{u}} (j : S' ⟶ S)

/-- An object of `Over S` whose structure morphism factors through a monomorphism
`j : S' ⟶ S` is isomorphic to the image of an object of `Over S'`. -/
def overMapIso [Mono j] {T : Over S} {U' : Over S'} (h : T ⟶ (Over.map j).obj U') :
    T ≅ (Over.map j).obj (Over.mk (h.left ≫ U'.hom)) :=
  Over.isoMk (Iso.refl _) (by
    have := Over.w h
    simp only [Over.map_obj_hom] at this
    simp [this])

/-- A monomorphism `U' → F ×_S S'` into the base change along a monomorphism `S' ⟶ S` is a
monomorphism `U' → F` after composing with `S' ⟶ S`. -/
lemma isMonoElement_map [Mono j] {U' : Over S'} (ξ : (baseChange j F).obj (op U'))
    (h : IsMonoElement (baseChange j F) ξ) :
    IsMonoElement F (U := (Over.map j).obj U') ξ := by
  intro T h₁ h₂ heq
  have w₂ : h₂.left ≫ U'.hom = h₁.left ≫ U'.hom := by
    rw [← cancel_mono j]
    have e₁ := Over.w h₁
    have e₂ := Over.w h₂
    simp only [Over.map_obj_hom] at e₁ e₂
    simp only [Category.assoc, e₁, e₂]
  let T' : Over S' := Over.mk (h₁.left ≫ U'.hom)
  let k₁ : T' ⟶ U' := Over.homMk h₁.left
  let k₂ : T' ⟶ U' := Over.homMk h₂.left w₂
  have e₁ : h₁ = (overMapIso j h₁).hom ≫ (Over.map j).map k₁ := by
    ext; simp [overMapIso, k₁]
  have e₂ : h₂ = (overMapIso j h₁).hom ≫ (Over.map j).map k₂ := by
    ext; simp [overMapIso, k₂]
  have hk : (baseChange j F).map k₁.op ξ = (baseChange j F).map k₂.op ξ := by
    rw [e₁, e₂] at heq
    simp only [op_comp, Functor.map_comp] at heq
    exact (F.mapIso (overMapIso j h₁).op).toEquiv.injective heq
  have := h k₁ k₂ hk
  rw [e₁, e₂, this]

/-- The spectrum of a local artinian ring has a single point. -/
lemma subsingleton_spec_of_isArtinianRing (A : Type u) [CommRing A] [IsLocalRing A]
    [IsArtinianRing A] : Subsingleton (Spec (CommRingCat.of A)) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum A))

/-- An infinitesimally étale morphism `U' → F ×_S S'` into the base change along an open
immersion `S' ⟶ S` is infinitesimally étale as a morphism `U' → F`. -/
lemma infinitesimallyEtaleAt_map [IsOpenImmersion j] {U' : Over S'}
    (ξ : (baseChange j F).obj (op U')) (y : U'.left)
    (h : InfinitesimallyEtaleAt (baseChange j F) ξ y) :
    InfinitesimallyEtaleAt F (U := (Over.map j).obj U') ξ y := by
  intro A _ _ _ f J hJ u₀ hu₀ v hv
  have hJtop : J ≠ ⊤ := by
    rintro rfl
    obtain ⟨n, hn⟩ := hJ
    rw [Ideal.top_pow] at hn
    exact top_ne_bot hn
  have : Nontrivial (A ⧸ J) := Ideal.Quotient.nontrivial_iff.mpr hJtop
  obtain ⟨x₀⟩ : Nonempty (Spec (CommRingCat.of (A ⧸ J))) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (A ⧸ J)))
  have hsub := subsingleton_spec_of_isArtinianRing A
  have hrange : Set.range f ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    have hz : z = Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ J))) x₀ := Subsingleton.elim _ _
    have hw := Over.w u₀
    simp only [Over.map_obj_hom, Over.mk_hom] at hw
    refine ⟨U'.hom (u₀.left x₀), ?_⟩
    rw [hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply,
      hw]
  obtain ⟨f', rfl⟩ : ∃ f', f' ≫ j = f := ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
  have hw₀ : u₀.left ≫ U'.hom = Spec.map (CommRingCat.ofHom (algebraMap A (A ⧸ J))) ≫ f' := by
    rw [← cancel_mono j]
    have hw := Over.w u₀
    simp only [Over.map_obj_hom, Over.mk_hom] at hw
    simp [hw]
  let u₀' : algebraOver f' (A ⧸ J) ⟶ U' := Over.homMk u₀.left hw₀
  have hiso : (BaseChange.mapAlgebraOverIso j f' (A ⧸ J)).inv ≫ (Over.map j).map u₀' = u₀ := by
    ext; simp [BaseChange.mapAlgebraOverIso, u₀']
  have hv' : (baseChange j F).map u₀'.op ξ =
      (baseChange j F).map (algebraOverBase f' (A ⧸ J)).op v := by
    apply (BaseChange.equiv j F f' (A ⧸ J)).injective
    let v' : (baseChange j F).obj (op (Over.mk f')) := v
    refine (BaseChange.equiv_apply j F f' (A ⧸ J) _).trans ?_
    refine Eq.trans ?_ (BaseChange.equiv_base j F f' (A ⧸ J) v').symm
    rw [← hv, ← hiso]
    change F.map _ (F.map ((Over.map j).map u₀').op ξ) = _
    rw [op_comp]
    exact (F.map_comp_apply _ _ _).symm
  obtain ⟨u', ⟨hu'₁, hu'₂⟩, hu'₃⟩ := h A f' J hJ u₀' hu₀ v hv'
  refine ⟨(Over.map j).map u', ⟨?_, hu'₂⟩, ?_⟩
  · ext
    have := congrArg CommaMorphism.left hu'₁
    simpa [algebraOverBase, u₀'] using this
  · rintro u ⟨hu₁, hu₂⟩
    have hwu : u.left ≫ U'.hom = f' := by
      rw [← cancel_mono j]
      have hw := Over.w u
      simp only [Over.map_obj_hom, Over.mk_hom] at hw
      simp [hw]
    let u'' : Over.mk f' ⟶ U' := Over.homMk u.left hwu
    have hu'' : (Over.map j).map u'' = u := by ext; simp [u'']
    rw [← hu'', hu'₃ u'' ⟨?_, ?_⟩]
    · ext
      have := congrArg CommaMorphism.left hu₁
      simpa [algebraOverBase, u₀', u''] using this
    · change F.map ((Over.map j).map u'').op ξ = v
      rw [hu'', hu₂]

end Charts

section Separated

variable {F : (Over S)ᵒᵖ ⥤ Type v} {Y : Scheme.{u}} {q : Y ⟶ S}

/-- The uniqueness part of the valuative criterion for the representing scheme, for a
valuative square whose bottom map factors through the local scheme at a point `s`. -/
lemma eq_of_local (e : F.RepresentableBy (Over.mk q)) {s : S}
    (hs : UnramifiedRepresentable (baseChange (S.fromSpecStalk s) F))
    {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R] {K : Type u} [Field K]
    [Algebra R K] [IsFractionRing R K] (φ : S.presheaf.stalk s ⟶ CommRingCat.of R)
    (l₁ l₂ : Spec (CommRingCat.of R) ⟶ Y)
    (h₁ : l₁ ≫ q = Spec.map φ ≫ S.fromSpecStalk s) (h₂ : l₂ ≫ q = Spec.map φ ≫ S.fromSpecStalk s)
    (hK : Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l₁ =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ l₂) : l₁ = l₂ := by
  obtain ⟨Ys, qs, ⟨es⟩, hsep, -, -⟩ := hs
  let T : Over (Spec (S.presheaf.stalk s)) := Over.mk (Spec.map φ)
  let m₁ : (Over.map (S.fromSpecStalk s)).obj T ⟶ Over.mk q := Over.homMk l₁ h₁
  let m₂ : (Over.map (S.fromSpecStalk s)).obj T ⟶ Over.mk q := Over.homMk l₂ h₂
  let x₁ : (baseChange (S.fromSpecStalk s) F).obj (op T) := e.homEquiv m₁
  let x₂ : (baseChange (S.fromSpecStalk s) F).obj (op T) := e.homEquiv m₂
  let n₁ : T ⟶ Over.mk qs := es.homEquiv.symm x₁
  let n₂ : T ⟶ Over.mk qs := es.homEquiv.symm x₂
  let α := Spec.map (CommRingCat.ofHom (algebraMap R K))
  let κ : Over.mk (α ≫ Spec.map φ) ⟶ T := Over.homMk α
  have hκ : κ ≫ n₁ = κ ≫ n₂ := by
    refine (es.comp_homEquiv_symm x₁ κ).trans (Eq.trans ?_ (es.comp_homEquiv_symm x₂ κ).symm)
    congr 1
    change F.map ((Over.map _).map κ).op (e.homEquiv m₁) =
      F.map ((Over.map _).map κ).op (e.homEquiv m₂)
    rw [← e.homEquiv_comp, ← e.homEquiv_comp]
    congr 1
    ext
    simpa [κ, m₁, m₂] using hK
  have hκ' := congrArg CommaMorphism.left hκ
  simp only [Over.comp_left, κ, Over.homMk_left] at hκ'
  have hsq : CommSq (α ≫ n₁.left) α qs (Spec.map φ) := ⟨by
    have := Over.w n₁
    simp only [Over.mk_hom, T] at this
    simp [this]⟩
  let V : ValuativeCommSq qs := ⟨R, K, α ≫ n₁.left, Spec.map φ, hsq⟩
  have hsub : Subsingleton V.commSq.LiftStruct := IsSeparated.valuativeCriterion qs V
  have hn : n₁.left = n₂.left := by
    have := hsub.elim ⟨n₁.left, rfl, by simpa [T] using Over.w n₁⟩
      ⟨n₂.left, hκ'.symm, by simpa [T] using Over.w n₂⟩
    exact congrArg CommSq.LiftStruct.l this
  have hn' : n₁ = n₂ := Over.OverMorphism.ext hn
  have hm : m₁ = m₂ := e.homEquiv.injective (es.homEquiv.symm.injective hn')
  exact congrArg CommaMorphism.left hm

/-- A presheaf represented by a scheme locally of finite type over a locally noetherian base,
whose base changes to the local schemes are represented by separated schemes, is
represented by a separated scheme. -/
lemma isSeparated_of_local [IsLocallyNoetherian S] [LocallyOfFiniteType q]
    (e : F.RepresentableBy (Over.mk q))
    (hloc : ∀ s : S, UnramifiedRepresentable (baseChange (S.fromSpecStalk s) F)) :
    IsSeparated q := by
  have := LocallyOfFiniteType.isLocallyNoetherian q
  apply IsSeparated.of_valuativeCriterion
  intro V
  constructor
  rintro ⟨l₁, hl₁, hl₁'⟩ ⟨l₂, hl₂, hl₂'⟩
  have hφ := Scheme.Spec_stalkClosedPointTo_fromSpecStalk V.i₂
  have := eq_of_local e (hloc _) (K := V.K) _ l₁ l₂ (hl₁'.trans hφ.symm) (hl₂'.trans hφ.symm)
    (hl₁.trans hl₂.symm)
  subst this
  rfl

end Separated

section Assemble

variable {F : (Over S)ᵒᵖ ⥤ Type v}

/-- Lemma 3 together with the separatedness argument: over a locally noetherian base, a
family of monomorphic, infinitesimally étale charts that are locally of finite type and
formally unramified, through which every field-valued point factors, makes `F` representable
by a separated, locally of finite type, formally unramified scheme, provided the local base
changes are representable in this way. -/
lemma unramifiedRepresentable_of_charts [IsLocallyNoetherian S]
    (hL3 : MurreChartGluingStatement.{u, v}) (hF : MurreConditions F)
    (hloc : ∀ s : S, UnramifiedRepresentable (baseChange (S.fromSpecStalk s) F))
    {ι : Type u} (U : ι → Over S) (ξ : ∀ i, F.obj (op (U i)))
    (hU : ∀ i, LocallyOfFiniteType (U i).hom ∧ FormallyUnramified (U i).hom ∧
        IsMonoElement F (ξ i) ∧ ∀ y, InfinitesimallyEtaleAt F (ξ i) y)
    (hcov : ∀ (K : Type u) [Field K] (f : Spec (CommRingCat.of K) ⟶ S)
        (η : F.obj (op (Over.mk f))), ∃ i, ∃ h : Over.mk f ⟶ U i, F.map h.op (ξ i) = η) :
    UnramifiedRepresentable F := by
  obtain ⟨hsmall, hzar, hff, hfilt, hadic, -⟩ := hF
  obtain ⟨Y, q, e, hlft, hopen, hcovY⟩ := hL3 S F hsmall hzar hff hfilt hadic ι U ξ
    (fun i => (hU i).1) (fun i => (hU i).2.2.1) (fun i => (hU i).2.2.2) hcov
  refine ⟨Y, q, ⟨e⟩, isSeparated_of_local e hloc, hlft, ?_⟩
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers ι (fun i => (U i).left)
    (fun i => (e.homEquiv.symm (ξ i)).left) (fun y => by
      obtain ⟨i, x, hx⟩ := hcovY y
      exact ⟨i, x, hx⟩) hopen
  have : IsZariskiLocalAtSource @FormallyUnramified.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FormallyUnramified)
  refine IsZariskiLocalAtSource.of_openCover (P := @FormallyUnramified.{u}) 𝒰 (fun i => ?_)
  have hw := Over.w (e.homEquiv.symm (ξ i))
  simp only [Over.mk_hom] at hw
  change FormallyUnramified ((e.homEquiv.symm (ξ i)).left ≫ q)
  rw [hw]
  exact (hU i).2.1

end Assemble

section Affine

/-- Base change along the identity is isomorphic to the presheaf itself. -/
def baseChangeIdIso (F : (Over S)ᵒᵖ ⥤ Type v) : baseChange (𝟙 S) F ≅ F :=
  Functor.isoWhiskerRight (NatIso.op (Over.mapId S)).symm F ≪≫ F.leftUnitor

/-- Murre's noetherian induction over an affine noetherian base: given the two steps,
Proposition 2 holds over `Spec R` for every noetherian ring `R`. The induction runs over the
ideals `J` of `R` (ordered by inclusion, which is well-founded upwards since `R` is
noetherian), the statement for `J` being Proposition 2 over the closed subscheme `Spec (R/J)`,
presented as `Spec A` for a surjection `R ⟶ A` with kernel `J`. -/
lemma unramifiedRepresentable_affine (hL3 : MurreChartGluingStatement.{u, v})
    (hNC : MurreNoetherianChartsStatement.{u, v}) (R : CommRingCat.{u}) [IsNoetherianRing R]
    (F : (Over (Spec R))ᵒᵖ ⥤ Type v) (hF : MurreConditions F)
    (hloc : ∀ s : Spec R, UnramifiedRepresentable (baseChange ((Spec R).fromSpecStalk s) F)) :
    UnramifiedRepresentable F := by
  suffices H : ∀ J : Ideal R, ∀ (A : CommRingCat.{u}) (φ : R ⟶ A), Function.Surjective φ →
      RingHom.ker φ.hom = J → UnramifiedRepresentable (baseChange (Spec.map φ) F) by
    have := H ⊥ R (𝟙 R) (fun x => ⟨x, rfl⟩) (by ext; simp)
    rw [Spec.map_id] at this
    exact unramifiedRepresentable_of_iso (baseChangeIdIso F) this
  intro J
  induction J using WellFoundedGT.induction with
  | _ J ih =>
  intro A φ hφ hker
  have : IsNoetherianRing A := isNoetherianRing_of_surjective R A φ.hom hφ
  let G := baseChange (Spec.map φ) F
  have hG : MurreConditions G := murreBaseChange _ _ _ F hF
  have hlocG : ∀ s : Spec A, UnramifiedRepresentable (baseChange ((Spec A).fromSpecStalk s) G) :=
    local_baseChange hloc (Spec.map φ)
  have hI : ∀ I : Ideal A, I ≠ ⊥ →
      UnramifiedRepresentable (baseChange (Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) G) := by
    intro I hI
    apply unramifiedRepresentable_of_iso (baseChangeCompIso _ _ F).symm
    rw [← Spec.map_comp]
    refine ih _ ?_ _ _ (Ideal.Quotient.mk_surjective.comp hφ) rfl
    have hcomp : RingHom.ker (φ ≫ CommRingCat.ofHom (Ideal.Quotient.mk I)).hom =
        I.comap φ.hom := by
      rw [CommRingCat.hom_comp, CommRingCat.hom_ofHom, ← RingHom.comap_ker, Ideal.mk_ker]
    rw [hcomp, ← hker, RingHom.ker_eq_comap_bot]
    refine lt_of_le_of_ne (Ideal.comap_mono bot_le) fun h => hI ?_
    exact (Ideal.comap_injective_of_surjective φ.hom hφ h).symm
  obtain ⟨ι, U, ξ, hU, hcov⟩ := hNC A G hG hlocG hI
  exact unramifiedRepresentable_of_charts hL3 hG hlocG U ξ hU hcov

end Affine

section General

/-- Proposition 2 from its two steps: cover the base by affine opens, which are spectra of
noetherian rings, apply the affine case on each, and glue the resulting representing schemes
by Lemma 3, using them as charts of `F`. -/
lemma unramifiedRepresentable_general (hL3 : MurreChartGluingStatement.{u, v})
    (hNC : MurreNoetherianChartsStatement.{u, v}) [IsLocallyNoetherian S]
    (F : (Over S)ᵒᵖ ⥤ Type v) (hF : MurreConditions F)
    (hloc : ∀ s : S, UnramifiedRepresentable (baseChange (S.fromSpecStalk s) F)) :
    UnramifiedRepresentable F := by
  let 𝒰 := S.affineOpenCover
  have hnoeth : ∀ j, IsNoetherianRing (𝒰.X j) := fun j => by
    have := isLocallyNoetherian_of_isOpenImmersion (𝒰.f j)
    exact isLocallyNoetherian_Spec.mp inferInstance
  have hrep : ∀ j, UnramifiedRepresentable (baseChange (𝒰.f j) F) := fun j =>
    unramifiedRepresentable_affine hL3 hNC (𝒰.X j) (baseChange (𝒰.f j) F)
      (murreBaseChange _ _ _ F hF) (local_baseChange hloc (𝒰.f j))
  choose Y q e hsep hlft hfu using hrep
  have e' : ∀ j, (baseChange (𝒰.f j) F).RepresentableBy (Over.mk (q j)) :=
    fun j => Classical.choice (e j)
  let U : 𝒰.I₀ → Over S := fun j => (Over.map (𝒰.f j)).obj (Over.mk (q j))
  let ξ : ∀ j, F.obj (op (U j)) := fun j => (e' j).homEquiv (𝟙 _)
  refine unramifiedRepresentable_of_charts hL3 hF hloc U ξ (fun j => ⟨?_, ?_, ?_, ?_⟩) ?_
  · change LocallyOfFiniteType (q j ≫ 𝒰.f j)
    infer_instance
  · change FormallyUnramified (q j ≫ 𝒰.f j)
    exact MorphismProperty.comp_mem @FormallyUnramified.{u} _ _ (hfu j) inferInstance
  · exact isMonoElement_map (𝒰.f j) (ξ j) (isMonoElement_of_representableBy (e' j))
  · exact fun y => infinitesimallyEtaleAt_map (𝒰.f j) (ξ j) y
      (infinitesimallyEtaleAt_of_representableBy (e' j) y)
  · intro K _ g η
    obtain ⟨z₀⟩ : Nonempty (Spec (CommRingCat.of K)) :=
      inferInstanceAs (Nonempty (PrimeSpectrum K))
    have hsub : Subsingleton (Spec (CommRingCat.of K)) :=
      inferInstanceAs (Subsingleton (PrimeSpectrum K))
    obtain ⟨j, hrange⟩ : ∃ j, Set.range g ⊆ Set.range (𝒰.f j) := by
      refine ⟨𝒰.idx (g z₀), ?_⟩
      rintro _ ⟨z, rfl⟩
      rw [Subsingleton.elim z z₀]
      exact 𝒰.covers (g z₀)
    obtain ⟨g', rfl⟩ : ∃ g', g' ≫ 𝒰.f j = g := ⟨_, IsOpenImmersion.lift_fac _ _ hrange⟩
    let η' : (baseChange (𝒰.f j) F).obj (op (Over.mk g')) := η
    refine ⟨j, (Over.map (𝒰.f j)).map ((e' j).homEquiv.symm η'), ?_⟩
    change (baseChange (𝒰.f j) F).map ((e' j).homEquiv.symm η').op ((e' j).homEquiv (𝟙 _)) = η'
    rw [← (e' j).homEquiv_comp, Category.comp_id, Equiv.apply_symm_apply]

end General

end LocalToGlobal

/-- Murre's Proposition 2 follows from Lemma 3 (`MurreChartGluingStatement`) and the
inductive step (`MurreNoetherianChartsStatement`). -/
theorem murreLocalToGlobal_of_steps (h : MurreLocalToGlobalStepsStatement.{u, v}) :
    MurreLocalToGlobalStatement.{u, v} := by
  intro S _ F hF hloc
  exact LocalToGlobal.unramifiedRepresentable_general h.1 h.2 F hF hloc

end Langlands.AlgebraicGeometry.UnramifiedFunctor
