import Langlands.AlgebraicGeometry.EtaleEquivalenceRelation
import Langlands.AlgebraicGeometry.AlgebraicSpace.SchemeLocalGeometry
import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
import Mathlib.AlgebraicGeometry.PullbackCarrier
import Mathlib.AlgebraicGeometry.Sites.Fpqc
import Mathlib.CategoryTheory.Sites.RegularEpi

/-! # Étale equivalence relations from presheaf kernel pairs

An étale map `a` from a scheme `U` over `S` to a presheaf `Y` on schemes over `S`, whose kernel
pair is represented by a scheme `R` over `S`, gives an étale equivalence relation on the
absolute scheme `U.left`. If `Y` is an fppf sheaf and `a` is surjective, an affine quotient of
this relation represents `Y`.
-/

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry

namespace AlgebraicSpace

variable {S : Scheme.{u}}

/-- A sieve containing a morphism whose underlying scheme morphism is flat, locally of finite
presentation and surjective is an fppf covering sieve. -/
theorem mem_fppfTopology_of_mem {T T' : Over S} (F : Sieve T) (p : T' ⟶ T) (hp : F p)
    [Flat p.left] [LocallyOfFinitePresentation p.left] [Surjective p.left] :
    F ∈ fppfTopology S T := by
  rw [GrothendieckTopology.mem_over_iff]
  refine Scheme.fppfTopology.superset_covering ?_
    (Precoverage.generate_mem_toGrothendieck p.left.singleton_mem_fppfPrecoverage)
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨⟩
  rw [Sieve.overEquiv_iff]
  have : (Over.homMk p.left : Over.mk (p.left ≫ T.hom) ⟶ T) =
      (Over.homMk (𝟙 T'.left) (by simp) : Over.mk (p.left ≫ T.hom) ⟶ T') ≫ p := by
    ext; simp
  rw [this]
  exact F.downward_closed hp _

/-- An étale surjective map from a scheme is locally surjective for the fppf topology. -/
theorem isLocallySurjective_of_isEtale {Y : Presheaf S} {U : Over S}
    (a : (schemeYoneda S).obj U ⟶ Y) (he : IsEtale a) (hs : IsSurjective a) :
    Presheaf.IsLocallySurjective (fppfTopology S) a := by
  constructor
  intro T y
  let g : (schemeYoneda S).obj T ⟶ Y := uliftYonedaEquiv.symm y
  let hr := he.representable
  have hsq := hr.isPullback g
  have : Etale (hr.snd g).left := he.projection g (hr.fst g) (hr.snd g) hsq
  have : Surjective (hr.snd g).left := hs.projection g (hr.fst g) (hr.snd g) hsq
  refine mem_fppfTopology_of_mem _ (hr.snd g) ⟨(hr.fst g).app _ ⟨𝟙 _⟩, ?_⟩
  have := types_congr_hom (NatTrans.congr_app hsq.w (op (hr.pullback g))) ⟨𝟙 _⟩
  simpa [g] using this

/-- The map of represented presheaves along a flat, locally finitely presented, surjective
morphism is locally surjective for the fppf topology. -/
theorem isLocallySurjective_map {U M : Over S} (q : U ⟶ M) [Flat q.left]
    [LocallyOfFinitePresentation q.left] [Surjective q.left] :
    Presheaf.IsLocallySurjective (fppfTopology S) ((schemeYoneda S).map q) := by
  constructor
  intro T m
  have hpb := (IsPullback.of_hasPullback m.down q).map (Over.forget S)
  have : Flat (pullback.fst m.down q).left :=
    MorphismProperty.of_isPullback (P := @Flat) hpb.flip ‹_›
  have : LocallyOfFinitePresentation (pullback.fst m.down q).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb.flip ‹_›
  have : Surjective (pullback.fst m.down q).left :=
    MorphismProperty.of_isPullback (P := @Surjective) hpb.flip ‹_›
  refine mem_fppfTopology_of_mem _ (pullback.fst m.down q) ⟨⟨pullback.snd m.down q⟩, ?_⟩
  simp [pullback.condition]

/-- If an fppf-locally surjective map from a scheme `U` to an fppf sheaf `Y` and a flat,
locally finitely presented, surjective morphism `q : U ⟶ M` have the same represented kernel
pair, then `M` represents `Y`. -/
theorem nonempty_iso_of_isPullback {Y : FppfSheaf S} {U R M : Over S} {t s : R ⟶ U}
    (a : (schemeYoneda S).obj U ⟶ Y.obj)
    (ha : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (ha' : Presheaf.IsLocallySurjective (fppfTopology S) a)
    (q : U ⟶ M) (hq : IsPullback t s q q)
    [Flat q.left] [LocallyOfFinitePresentation q.left] [Surjective q.left] :
    Nonempty ((schemeYoneda S).obj M ≅ Y.obj) := by
  let J := fppfTopology S
  let aS : (schemeSheaf S).obj U ⟶ Y := ObjectProperty.homMk a
  have haS : IsPullback ((schemeSheaf S).map t) ((schemeSheaf S).map s) aS aS :=
    IsPullback.of_map_of_faithful (F := sheafToPresheaf J (Type (u + 1))) ha
  have hqS : IsPullback ((schemeSheaf S).map t) ((schemeSheaf S).map s)
      ((schemeSheaf S).map q) ((schemeSheaf S).map q) :=
    IsPullback.of_map_of_faithful (F := sheafToPresheaf J (Type (u + 1))) (hq.map (schemeYoneda S))
  have : Sheaf.IsLocallySurjective aS := ha'
  have : Sheaf.IsLocallySurjective ((schemeSheaf S).map q) := isLocallySurjective_map q
  have : IsRegularEpi aS := IsRegularEpiCategory.regularEpiOfEpi aS
  have : IsRegularEpi ((schemeSheaf S).map q) :=
    IsRegularEpiCategory.regularEpiOfEpi ((schemeSheaf S).map q)
  have hcA : IsColimit (Cofork.ofπ (f := (schemeSheaf S).map t) (g := (schemeSheaf S).map s)
      aS haS.w) := isColimitCoforkOfEffectiveEpi aS haS.cone haS.isLimit
  have hcQ : IsColimit (Cofork.ofπ (f := (schemeSheaf S).map t) (g := (schemeSheaf S).map s)
      ((schemeSheaf S).map q) hqS.w) :=
    isColimitCoforkOfEffectiveEpi ((schemeSheaf S).map q) hqS.cone hqS.isLimit
  exact ⟨(sheafToPresheaf J (Type (u + 1))).mapIso (hcQ.coconePointUniqueUpToIso hcA)⟩

/-- A property of scheme morphisms that is stable under base change is stable under base change
for morphisms of schemes over `S`. -/
instance isStableUnderBaseChange_inverseImage_forget {P : MorphismProperty Scheme.{u}}
    [P.IsStableUnderBaseChange] : (P.inverseImage (Over.forget S)).IsStableUnderBaseChange where
  of_isPullback sq hg := P.of_isPullback (sq.map (Over.forget S)) hg

/-- Two points of schemes over `S` with the same image lift to a point of a pullback. -/
theorem exists_preimage_of_isPullback {P A B C : Over S} {fst : P ⟶ A} {snd : P ⟶ B}
    {f : A ⟶ C} {g : B ⟶ C} (h : IsPullback fst snd f g) (x : A.left) (y : B.left)
    (hxy : f.left x = g.left y) : ∃ z : P.left, fst.left z = x ∧ snd.left z = y := by
  have h' : IsPullback fst.left snd.left f.left g.left := h.map (Over.forget S)
  obtain ⟨z, hz₁, hz₂⟩ := Scheme.Pullback.exists_preimage_pullback x y hxy
  refine ⟨h'.isoPullback.inv z, ?_, ?_⟩
  · rw [← Scheme.Hom.comp_apply, h'.isoPullback_inv_fst, hz₁]
  · rw [← Scheme.Hom.comp_apply, h'.isoPullback_inv_snd, hz₂]

/-- The functor of points reflects pullback squares of schemes over `S`. -/
theorem isPullback_of_map {P A B C : Over S} {fst : P ⟶ A} {snd : P ⟶ B}
    {f : A ⟶ C} {g : B ⟶ C}
    (h : IsPullback ((schemeYoneda S).map fst) ((schemeYoneda S).map snd)
      ((schemeYoneda S).map f) ((schemeYoneda S).map g)) : IsPullback fst snd f g :=
  h.of_map_of_faithful

/-- The map of represented presheaves along an étale morphism is étale. -/
theorem isEtale_map {U V : Over S} (j : U ⟶ V) (hj : Etale j.left) :
    IsEtale ((schemeYoneda S).map j) := by
  have : (MorphismProperty.inverseImage (@Etale.{u}) (Over.forget S)).IsStableUnderBaseChange :=
    isStableUnderBaseChange_inverseImage_forget
  exact MorphismProperty.relative_map (P := MorphismProperty.inverseImage (@Etale.{u})
    (Over.forget S)) hj

set_option backward.isDefEq.respectTransparency.types false in
/-- Étale maps of presheaves are stable under composition. -/
theorem IsEtale.comp {F G H : Presheaf S} {f : F ⟶ G} {g : G ⟶ H} (hf : IsEtale f)
    (hg : IsEtale g) : IsEtale (f ≫ g) :=
  MorphismProperty.comp_mem (W := (MorphismProperty.inverseImage (@Etale.{u})
    (Over.forget S)).relative (schemeYoneda S)) f g hf hg

/-- A representable map `a` from a scheme to a presheaf `Y` is surjective if `Y` has a surjective
map `c` from a scheme along which some represented base change of `a` is surjective. -/
theorem isSurjective_of_isPullback {Y : Presheaf S} {U V W : Over S}
    {a : (schemeYoneda S).obj U ⟶ Y} (ha : IsRepresentableMorphism a)
    {c : (schemeYoneda S).obj V ⟶ Y} (hc : IsSurjective c)
    {w : (schemeYoneda S).obj W ⟶ (schemeYoneda S).obj U} {p : W ⟶ V}
    (hw : IsPullback w ((schemeYoneda S).map p) a c) (hp : Surjective p.left) :
    IsSurjective a := by
  refine ⟨ha, fun T P g a' pT hsq => ?_⟩
  change Surjective pT.left
  refine ⟨fun x => ?_⟩
  let hr := hc.representable
  have hQ := hr.isPullback g
  obtain ⟨κ, hκ⟩ := (schemeYoneda S).map_surjective (hr.fst g)
  have : Surjective (hr.snd g).left := hc.projection g _ _ hQ
  obtain ⟨y, hy⟩ := Surjective.surj (f := (hr.snd g).left) x
  obtain ⟨w₀, hw₀⟩ := Surjective.surj (f := p.left) (κ.left y)
  obtain ⟨z, hz₁, -⟩ :=
    exists_preimage_of_isPullback (IsPullback.of_hasPullback κ p) y w₀ hw₀.symm
  have hcomm : ((schemeYoneda S).map (pullback.snd κ p) ≫ w) ≫ a =
      (schemeYoneda S).map (pullback.fst κ p ≫ hr.snd g) ≫ g := by
    simp only [Category.assoc, hw.w, Functor.map_comp, ← hQ.w, ← hκ]
    simp only [← Functor.map_comp_assoc, pullback.condition]
  obtain ⟨φ, hφ⟩ := (schemeYoneda S).map_surjective (hsq.lift _ _ hcomm)
  have hφ₂ : φ ≫ pT = pullback.fst κ p ≫ hr.snd g :=
    (schemeYoneda S).map_injective (by rw [Functor.map_comp, hφ, hsq.lift_snd])
  refine ⟨φ.left z, ?_⟩
  rw [← Scheme.Hom.comp_apply, ← Over.comp_left, hφ₂, Over.comp_left, Scheme.Hom.comp_apply, hz₁,
    hy]

/-- If a presheaf `Y` has an étale surjective map from a scheme and a surjective map `c` from an
affine scheme, then `Y` has an étale surjective map from an affine scheme. -/
theorem exists_affine_atlas {Y : Presheaf S} {U V : Over S} [IsAffine V.left]
    (a : (schemeYoneda S).obj U ⟶ Y) (ha : IsEtale a) (has : IsSurjective a)
    (c : (schemeYoneda S).obj V ⟶ Y) (hc : IsSurjective c) :
    ∃ (U₀ : Over S) (a₀ : (schemeYoneda S).obj U₀ ⟶ Y),
      IsAffine U₀.left ∧ IsEtale a₀ ∧ IsSurjective a₀ := by
  let hr := ha.representable
  have hP := hr.isPullback c
  obtain ⟨π, hπ⟩ := (schemeYoneda S).map_surjective (hr.fst c)
  rw [← hπ] at hP
  let ρ := hr.snd c
  have : Etale ρ.left := ha.projection c _ _ hP
  have : Surjective ρ.left := has.projection c _ _ hP
  let 𝒰 := U.left.affineCover
  let G : 𝒰.I₀ → Set V.left := fun x => ρ.left '' (π.left ⁻¹' Set.range (𝒰.f x))
  have hG : ∀ x, IsOpen (G x) := fun x =>
    ρ.left.isOpenMap _ ((𝒰.f x).isOpenEmbedding.isOpen_range.preimage π.left.continuous)
  have hcov : Set.univ ⊆ ⋃ x, G x := by
    intro v _
    obtain ⟨p, rfl⟩ := Surjective.surj (f := ρ.left) v
    exact Set.mem_iUnion.2 ⟨𝒰.idx (π.left p), p, 𝒰.covers (π.left p), rfl⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover G hG hcov
  let g : t → Scheme.{u} := fun i => 𝒰.X i
  let J : ∐ g ⟶ U.left := Sigma.desc fun i => 𝒰.f i
  have : IsZariskiLocalAtSource @Etale.{u} :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @Etale.{u})
  have hJ : Etale J := IsZariskiLocalAtSource.sigmaDesc fun i => inferInstance
  let U₀ : Over S := Over.mk (J ≫ U.hom)
  let j : U₀ ⟶ U := Over.homMk J
  have he : IsEtale ((schemeYoneda S).map j ≫ a) := (isEtale_map j hJ).comp ha
  refine ⟨U₀, (schemeYoneda S).map j ≫ a, inferInstanceAs (IsAffine (∐ g)), he, ?_⟩
  have hW := IsPullback.of_hasPullback j π
  have hsq := (hW.map (schemeYoneda S)).paste_vert hP
  rw [← Functor.map_comp] at hsq
  refine isSurjective_of_isPullback he.representable hc hsq ⟨fun v => ?_⟩
  obtain ⟨i, hi, hv⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ v))
  obtain ⟨p, ⟨y, hy⟩, rfl⟩ := hv
  obtain ⟨z, -, hz⟩ := exists_preimage_of_isPullback hW (Sigma.ι g ⟨i, hi⟩ y) p (by
    change (Sigma.ι g ⟨i, hi⟩ ≫ J) y = π.left p
    rw [Sigma.ι_comp_desc, hy])
  refine ⟨z, ?_⟩
  rw [Over.comp_left, Scheme.Hom.comp_apply, hz]

/-- An étale map from a scheme to a presheaf has a represented kernel pair with étale
projections. -/
theorem exists_kernelPair {Y : Presheaf S} {U : Over S} {a : (schemeYoneda S).obj U ⟶ Y}
    (ha : IsEtale a) :
    ∃ (R : Over S) (t s : R ⟶ U),
      IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a ∧
        Etale t.left ∧ Etale s.left := by
  let hr := ha.representable
  obtain ⟨t, ht⟩ := (schemeYoneda S).map_surjective (hr.fst a)
  have h := hr.isPullback a
  rw [← ht] at h
  exact ⟨hr.pullback a, t, hr.snd a, h, ha.projection a _ _ h.flip, ha.projection a _ _ h⟩

end AlgebraicSpace

namespace EtaleEquivalenceRelation

open AlgebraicSpace

variable {S : Scheme.{u}} {U R : Over S} {t s : R ⟶ U} {Y : AlgebraicSpace.Presheaf S}
  {a : (schemeYoneda S).obj U ⟶ Y}

/-- Lifting a pair of points with equal images to the kernel pair. -/
theorem exists_lift_of_isPullback
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    {T : Over S} (x y : T ⟶ U)
    (w : (schemeYoneda S).map x ≫ a = (schemeYoneda S).map y ≫ a) :
    ∃ r : T ⟶ R, r ≫ t = x ∧ r ≫ s = y := by
  obtain ⟨r, hr⟩ := (schemeYoneda S).map_surjective (h.lift _ _ w)
  refine ⟨r, (schemeYoneda S).map_injective ?_, (schemeYoneda S).map_injective ?_⟩
  · rw [Functor.map_comp, hr, h.lift_fst]
  · rw [Functor.map_comp, hr, h.lift_snd]

/-- Points of the kernel pair are determined by their two projections. -/
theorem hom_ext_of_isPullback
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    {T : Over S} {r r' : T ⟶ R} (ht : r ≫ t = r' ≫ t) (hs : r ≫ s = r' ≫ s) : r = r' := by
  apply (schemeYoneda S).map_injective
  apply h.hom_ext
  · rw [← Functor.map_comp, ← Functor.map_comp, ht]
  · rw [← Functor.map_comp, ← Functor.map_comp, hs]

/-- The étale equivalence relation on `U.left` given by a represented kernel pair of a map to
a presheaf, with étale projections. -/
def ofKernelPair (t s : R ⟶ U) (a : (schemeYoneda S).obj U ⟶ Y)
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (ht : Etale t.left) (hs : Etale s.left) : EtaleEquivalenceRelation.{u} where
  U := U.left
  R := R.left
  t := t.left
  s := s.left
  mono_lift := by
    constructor
    intro Z g g' e
    have e₁ : g ≫ t.left = g' ≫ t.left := by
      simpa using congrArg (· ≫ prod.fst) e
    have e₂ : g ≫ s.left = g' ≫ s.left := by
      simpa using congrArg (· ≫ prod.snd) e
    have w : g' ≫ R.hom = g ≫ R.hom := by
      rw [← Over.w t, reassoc_of% e₁]
    let T : Over S := Over.mk (g ≫ R.hom)
    let G : T ⟶ R := Over.homMk g
    let G' : T ⟶ R := Over.homMk g' w
    have := hom_ext_of_isPullback h (r := G) (r' := G') (by ext; exact e₁) (by ext; exact e₂)
    exact congrArg CommaMorphism.left this
  refl := by
    intro T x
    obtain ⟨r, hr₁, hr₂⟩ := exists_lift_of_isPullback h
      (Over.homMk x : Over.mk (x ≫ U.hom) ⟶ U) (Over.homMk x) rfl
    exact ⟨r.left, by simpa using congrArg CommaMorphism.left hr₁,
      by simpa using congrArg CommaMorphism.left hr₂⟩
  symm := by
    intro T r
    obtain ⟨r', hr₁, hr₂⟩ := exists_lift_of_isPullback h
      ((Over.homMk r : Over.mk (r ≫ R.hom) ⟶ R) ≫ s) (Over.homMk r ≫ t)
      (by simp only [Functor.map_comp, Category.assoc, h.w])
    exact ⟨r'.left, by simpa using congrArg CommaMorphism.left hr₁,
      by simpa using congrArg CommaMorphism.left hr₂⟩
  trans := by
    intro T r r' e
    have w : r' ≫ R.hom = r ≫ R.hom := by
      rw [← Over.w t, ← reassoc_of% e, Over.w s, Over.w t]
    let ρ : Over.mk (r ≫ R.hom) ⟶ R := Over.homMk r
    let ρ' : Over.mk (r ≫ R.hom) ⟶ R := Over.homMk r' w
    have e' : ρ ≫ s = ρ' ≫ t := by ext; exact e
    obtain ⟨r'', hr₁, hr₂⟩ := exists_lift_of_isPullback h (ρ ≫ t) (ρ' ≫ s) (by
      simp only [Functor.map_comp, Category.assoc, h.w]
      rw [← Functor.map_comp_assoc, e', Functor.map_comp_assoc, h.w])
    exact ⟨r''.left, by simpa [ρ] using congrArg CommaMorphism.left hr₁,
      by simpa [ρ'] using congrArg CommaMorphism.left hr₂⟩
  etale_t := ht
  etale_s := hs

/-- Let `a` be an étale surjective map from a scheme with represented kernel pair `(t, s)`, and
let `c` be a finite surjective map from an affine scheme `V` to the same presheaf. Then the
relation of `a` has a finite surjective cartesian cover by a relation with an affine quotient:
the relation of the induced étale cover `U ×_Y V ⟶ V`, whose quotient is `V`. -/
theorem ofKernelPair_hasFiniteSurjectiveCoverWithAffineQuotient
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (ht : Etale t.left) (hs : Etale s.left) (he : IsEtale a) (hsurj : IsSurjective a)
    {V : Over S} [IsAffine V.left] (c : (schemeYoneda S).obj V ⟶ Y)
    (hc : AlgebraicSpace.IsFinite c) (hcs : IsSurjective c) :
    (ofKernelPair t s a h ht hs).HasFiniteSurjectiveCoverWithAffineQuotient := by
  let hr := he.representable
  have hU := hr.isPullback c
  obtain ⟨φ, hφ⟩ := (schemeYoneda S).map_surjective (hr.fst c)
  rw [← hφ] at hU
  let q := hr.snd c
  have hqe : Etale q.left := he.projection c _ _ hU
  have hqs : Surjective q.left := hsurj.projection c _ _ hU
  have hφf : _root_.AlgebraicGeometry.IsFinite φ.left := hc.projection a _ _ hU.flip
  have hφs : Surjective φ.left := hcs.projection a _ _ hU.flip
  have hR := IsPullback.of_hasPullback q q
  have hRS : IsPullback (pullback.fst q q).left (pullback.snd q q).left q.left q.left :=
    hR.map (Over.forget S)
  have ht' : Etale (pullback.fst q q).left :=
    MorphismProperty.of_isPullback (P := @Etale) hRS.flip hqe
  have hs' : Etale (pullback.snd q q).left := MorphismProperty.of_isPullback (P := @Etale) hRS hqe
  obtain ⟨g, hg₁, hg₂⟩ := exists_lift_of_isPullback h (pullback.fst q q ≫ φ)
    (pullback.snd q q ≫ φ) (by
      simp only [Functor.map_comp, Category.assoc, hU.w]
      simp only [← Functor.map_comp_assoc]
      rw [show pullback.fst q q ≫ q = pullback.snd q q ≫ q from pullback.condition])
  refine ⟨ofKernelPair _ _ _ (hR.map (schemeYoneda S)) ht' hs', φ.left, g.left, ⟨?_, ?_⟩, hφf,
    hφs, ?_⟩
  · change g.left ≫ t.left = (pullback.fst q q).left ≫ φ.left
    rw [← Over.comp_left, hg₁, Over.comp_left]
  · have big := (hR.map (schemeYoneda S)).paste_horiz hU
    rw [← Functor.map_comp, ← hg₁, Functor.map_comp, ← hU.w] at big
    have hsq : IsPullback g (pullback.snd q q) s φ :=
      isPullback_of_map (big.of_right (by rw [← Functor.map_comp, ← Functor.map_comp, hg₂]) h)
    exact hsq.map (Over.forget S)
  · have : Etale q.left := hqe
    have hfl : Flat q.left := inferInstance
    have hlfp : LocallyOfFinitePresentation q.left := inferInstance
    exact ⟨V.left, q.left, inferInstance, hRS, hfl, hlfp, hqs⟩

/-- If the relation of an étale surjective map `a` from a scheme to an fppf sheaf `Y` has an
affine quotient, then `Y` is represented by an affine scheme over `S`. -/
theorem exists_isAffine_iso_of_hasAffineQuotient {Y : FppfSheaf S}
    {a : (schemeYoneda S).obj U ⟶ Y.obj}
    (h : IsPullback ((schemeYoneda S).map t) ((schemeYoneda S).map s) a a)
    (ht : Etale t.left) (hs : Etale s.left) (he : IsEtale a) (hsurj : IsSurjective a)
    (hq : (ofKernelPair t s a h ht hs).HasAffineQuotient) :
    ∃ M : Over S, IsAffine M.left ∧ Nonempty ((schemeYoneda S).obj M ≅ Y.obj) := by
  obtain ⟨M, q, hM, hpb, hfl, hlfp, hqs⟩ := hq
  change IsPullback t.left s.left q q at hpb
  change U.left ⟶ M at q
  have : Flat q := hfl
  have : LocallyOfFinitePresentation q := hlfp
  have : Surjective q := hqs
  have hdesc : ∀ {Z : Scheme.{u}} (g₁ g₂ : Z ⟶ U.left), g₁ ≫ q = g₂ ≫ q →
      g₁ ≫ U.hom = g₂ ≫ U.hom := fun g₁ g₂ hg =>
    calc g₁ ≫ U.hom = hpb.lift g₁ g₂ hg ≫ t.left ≫ U.hom := by
          rw [← Category.assoc, hpb.lift_fst]
      _ = hpb.lift g₁ g₂ hg ≫ s.left ≫ U.hom := by rw [Over.w t, Over.w s]
      _ = g₂ ≫ U.hom := by rw [← Category.assoc, hpb.lift_snd]
  let m : M ⟶ S := EffectiveEpi.desc q U.hom hdesc
  let M' : Over S := Over.mk m
  let q' : U ⟶ M' := Over.homMk q (EffectiveEpi.fac q U.hom hdesc)
  have hq' : IsPullback t s q' q' :=
    IsPullback.of_map_of_faithful (F := Over.forget S) hpb
  have : Flat q'.left := hfl
  have : LocallyOfFinitePresentation q'.left := hlfp
  have : Surjective q'.left := hqs
  exact ⟨M', hM, nonempty_iso_of_isPullback a h (isLocallySurjective_of_isEtale a he hsurj) q' hq'⟩

end EtaleEquivalenceRelation

end Langlands.AlgebraicGeometry
