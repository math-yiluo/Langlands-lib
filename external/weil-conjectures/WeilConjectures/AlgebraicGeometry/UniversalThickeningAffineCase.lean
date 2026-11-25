/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.UniversalFirstOrderThickening
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Spectra of universal square-zero algebra extensions

Source: Stacks Project, More on Morphisms, proof of Lemma 04F3, affine-case paragraph,
using Algebra, Lemma 04EB (blueprint: lem-weil-pbc-universal-thickening-affine-case).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The ring homomorphism corresponding to a morphism into a spectrum. -/
private noncomputable def specRingHom {T : Scheme.{u}} {B : Type u} [CommRing B]
    (f : T ⟶ Spec (.of B)) : B →+* Γ(T, ⊤) :=
  ((Scheme.ΓSpecIso (.of B)).inv ≫ f.appTop).hom

/-- Naturality in the source scheme. -/
private theorem specRingHom_comp {T T' : Scheme.{u}} {B : Type u} [CommRing B]
    (j : T ⟶ T') (f : T' ⟶ Spec (.of B)) :
    specRingHom (j ≫ f) = j.appTop.hom.comp (specRingHom f) := by
  simp only [specRingHom, Scheme.Hom.comp_appTop]
  rfl

/-- Naturality in the spectrum ring. -/
private theorem specRingHom_spec {T : Scheme.{u}} {B C : Type u}
    [CommRing B] [CommRing C] (f : T ⟶ Spec (.of B)) (φ : C →+* B) :
    specRingHom (f ≫ Spec.map (CommRingCat.ofHom φ)) = (specRingHom f).comp φ := by
  simp only [specRingHom, Scheme.Hom.comp_appTop,
    ← Category.assoc, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/-- A morphism into a spectrum is determined by its map on global sections. -/
private theorem specRingHom_injective {T : Scheme.{u}} {B : Type u} [CommRing B] :
    Function.Injective (specRingHom (T := T) (B := B)) := by
  intro f g h
  apply ext_to_Spec
  exact CommRingCat.hom_ext h

/-- Every ring homomorphism to global sections determines a morphism into the spectrum. -/
private theorem specRingHom_lift {T : Scheme.{u}} {B : Type u} [CommRing B]
    (φ : B →+* Γ(T, ⊤)) :
    ∃ f : T ⟶ Spec (.of B), specRingHom f = φ := by
  refine ⟨ΓSpec.adjunction.homEquiv T (.op (.of B)) (CommRingCat.ofHom φ).op, ?_⟩
  exact congrArg CommRingCat.Hom.hom (ΓSpecIso_inv_ΓSpec_adjunction_homEquiv _)

/-- Open base change preserves a first order thickening: its kernel ideals are
transported by the isomorphism on sections of the open immersion. -/
private theorem firstOrderThickening_pullback_open
    {T T' U U' : Scheme.{u}} (j : T ⟶ T') (jU : U ⟶ U')
    (f : U ⟶ T) (g : U' ⟶ T') [IsOpenImmersion g]
    (H : IsPullback jU f g j) (hj : IsFirstOrderThickening j) :
    IsFirstOrderThickening jU := by
  have : IsClosedImmersion j := hj.1
  have : IsClosedImmersion jU := MorphismProperty.of_isPullback H.flip inferInstance
  refine ⟨inferInstance, ?_⟩
  apply Scheme.IdealSheafData.ext
  funext V
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply]
  rw [Scheme.ker_ideal_of_isPullback_of_isOpenImmersion j jU f g H]
  apply le_bot_iff.mp
  apply (Ideal.le_comap_pow _ _).trans
  have hz := congrArg (fun J => J.ideal
    ⟨g ''ᵁ V, V.2.image_of_isOpenImmersion g⟩) hj.2
  simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
    Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] at hz
  rw [hz]
  exact (Ideal.comap_bot_of_injective _
    (ConcreteCategory.bijective_of_isIso (g.appIso V).inv).1).le

/-- Uniqueness on affine test schemes gives uniqueness on any test scheme, by
restricting both solutions to an affine cover of the thickened test scheme. -/
private theorem unique_lifts_of_affine_tests
    {Z Z' X : Scheme.{u}} (h : Z ⟶ X) (i : Z ⟶ Z') (h' : Z' ⟶ X)
    (H : ∀ {T T' : Scheme.{u}} [IsAffine T'] (j : T ⟶ T')
      (b : T' ⟶ X) (a : T ⟶ Z), IsFirstOrderThickening j → j ≫ b = a ≫ h →
        ∃! c : T' ⟶ Z', c ≫ h' = b ∧ j ≫ c = a ≫ i)
    {T T' : Scheme.{u}} (j : T ⟶ T') (b : T' ⟶ X) (a : T ⟶ Z)
    (hj : IsFirstOrderThickening j) (hab : j ≫ b = a ≫ h)
    {c d : T' ⟶ Z'} (hc : c ≫ h' = b ∧ j ≫ c = a ≫ i)
    (hd : d ≫ h' = b ∧ j ≫ d = a ≫ i) : c = d := by
  let C := T'.affineCover
  apply C.hom_ext
  intro k
  have hlocal : IsFirstOrderThickening (C.pullbackHom j k) :=
    firstOrderThickening_pullback_open j (C.pullbackHom j k)
      ((C.pullback₁ j).f k) (C.f k)
      (IsPullback.of_hasPullback j (C.f k)).flip hj
  have hablocal : C.pullbackHom j k ≫ (C.f k ≫ b) =
      ((C.pullback₁ j).f k ≫ a) ≫ h := by
    rw [← Category.assoc, C.pullbackHom_map, Category.assoc, hab, Category.assoc]
  apply (H (C.pullbackHom j k) (C.f k ≫ b) ((C.pullback₁ j).f k ≫ a)
    hlocal hablocal).unique
  · constructor
    · rw [Category.assoc, hc.1]
    · rw [← Category.assoc, C.pullbackHom_map, Category.assoc, hc.2, Category.assoc]
  · constructor
    · rw [Category.assoc, hd.1]
    · rw [← Category.assoc, C.pullbackHom_map, Category.assoc, hd.2, Category.assoc]

/-- Unique solutions on affine tests glue. First establish uniqueness on arbitrary
schemes; use it on overlaps, glue the local lifts, and check both triangles locally. -/
private theorem lifts_of_affine_tests
    {Z Z' X : Scheme.{u}} (h : Z ⟶ X) (i : Z ⟶ Z') (h' : Z' ⟶ X)
    (H : ∀ {T T' : Scheme.{u}} [IsAffine T'] (j : T ⟶ T')
      (b : T' ⟶ X) (a : T ⟶ Z), IsFirstOrderThickening j → j ≫ b = a ≫ h →
        ∃! c : T' ⟶ Z', c ≫ h' = b ∧ j ≫ c = a ≫ i)
    {T T' : Scheme.{u}} (j : T ⟶ T') (b : T' ⟶ X) (a : T ⟶ Z)
    (hj : IsFirstOrderThickening j) (hab : j ≫ b = a ≫ h) :
    ∃! c : T' ⟶ Z', c ≫ h' = b ∧ j ≫ c = a ≫ i := by
  classical
  let C := T'.affineCover
  have local_lift (k : C.I₀) : ∃! c : C.X k ⟶ Z',
      c ≫ h' = C.f k ≫ b ∧ C.pullbackHom j k ≫ c = ((C.pullback₁ j).f k ≫ a) ≫ i := by
    apply H
    · exact firstOrderThickening_pullback_open j (C.pullbackHom j k)
        ((C.pullback₁ j).f k) (C.f k)
        (IsPullback.of_hasPullback j (C.f k)).flip hj
    · rw [← Category.assoc, C.pullbackHom_map, Category.assoc, hab, Category.assoc]
  choose c hc using fun k => (local_lift k).exists
  have compat (k l : C.I₀) :
      Limits.pullback.fst (C.f k) (C.f l) ≫ c k =
      Limits.pullback.snd (C.f k) (C.f l) ≫ c l := by
    let p₁ := Limits.pullback.fst (C.f k) (C.f l)
    let p₂ := Limits.pullback.snd (C.f k) (C.f l)
    let e := p₁ ≫ C.f k
    let jP := Limits.pullback.snd j e
    let tP := Limits.pullback.fst j e
    have he : p₁ ≫ C.f k = p₂ ≫ C.f l := Limits.pullback.condition
    have hP : IsFirstOrderThickening jP :=
      firstOrderThickening_pullback_open j jP tP e
        (IsPullback.of_hasPullback j e).flip hj
    have w₁ : tP ≫ j = (jP ≫ p₁) ≫ C.f k := by
      simpa only [Category.assoc] using (Limits.pullback.condition (f := j) (g := e))
    have w₂ : tP ≫ j = (jP ≫ p₂) ≫ C.f l := by
      rw [Category.assoc, ← he]
      exact Limits.pullback.condition
    let u₁ := Limits.pullback.lift tP (jP ≫ p₁) w₁
    let u₂ := Limits.pullback.lift tP (jP ≫ p₂) w₂
    have fac₁ : jP ≫ (p₁ ≫ c k) = (tP ≫ a) ≫ i := by
      calc
        _ = u₁ ≫ (C.pullbackHom j k ≫ c k) := by
          simp only [u₁, Scheme.Cover.pullbackHom, Limits.pullback.lift_snd_assoc,
            Category.assoc]
        _ = u₁ ≫ (((C.pullback₁ j).f k ≫ a) ≫ i) := by rw [(hc k).2]
        _ = (tP ≫ a) ≫ i := by
          change u₁ ≫ ((Limits.pullback.fst j (C.f k) ≫ a) ≫ i) = (tP ≫ a) ≫ i
          simp only [Category.assoc, u₁, Limits.pullback.lift_fst_assoc]
    have fac₂ : jP ≫ (p₂ ≫ c l) = (tP ≫ a) ≫ i := by
      calc
        _ = u₂ ≫ (C.pullbackHom j l ≫ c l) := by
          simp only [u₂, Scheme.Cover.pullbackHom, Limits.pullback.lift_snd_assoc,
            Category.assoc]
        _ = u₂ ≫ (((C.pullback₁ j).f l ≫ a) ≫ i) := by rw [(hc l).2]
        _ = (tP ≫ a) ≫ i := by
          change u₂ ≫ ((Limits.pullback.fst j (C.f l) ≫ a) ≫ i) = (tP ≫ a) ≫ i
          simp only [Category.assoc, u₂, Limits.pullback.lift_fst_assoc]
    apply unique_lifts_of_affine_tests h i h' H jP (e ≫ b) (tP ≫ a) hP
    · rw [← Category.assoc, ← Limits.pullback.condition (f := j) (g := e),
        Category.assoc, hab,
        Category.assoc]
    · exact ⟨by rw [Category.assoc, (hc k).1, ← Category.assoc], fac₁⟩
    · exact ⟨by rw [Category.assoc, (hc l).1, ← Category.assoc, ← he], fac₂⟩
  let c' := C.glueMorphisms c compat
  have hc' : c' ≫ h' = b ∧ j ≫ c' = a ≫ i := by
    constructor
    · apply C.hom_ext
      intro k
      simpa only [c', C.ι_glueMorphisms_assoc] using (hc k).1
    · apply Scheme.Cover.hom_ext (C.pullback₁ j)
      intro k
      change C.I₀ at k
      rw [← C.pullbackHom_map_assoc,
        show C.f k ≫ c' = c k from C.ι_glueMorphisms c compat k]
      simpa only [Category.assoc] using (hc k).2
  exact ⟨c', hc', fun d hd => unique_lifts_of_affine_tests h i h' H j b a hj hab hd hc'⟩

/-- Translate an affine test to the quotient of its global sections by the kernel
of the closed immersion, apply the ring universal property, and translate back. -/
private theorem affine_lift
    (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S']
    (φ : R →+* S) [Algebra R S] [Algebra R S'] (π : S' →ₐ[R] S)
    (hφ : algebraMap R S = φ)
    (hUniversal : ∀ (A : Type u) [CommRing A] [Algebra R A] (I : Ideal A),
      I ^ 2 = ⊥ → ∀ a : S →ₐ[R] A ⧸ I,
        ∃! a' : S' →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp a' = a.comp π)
    {T T' : Scheme.{u}} [IsAffine T'] (j : T ⟶ T')
    (b : T' ⟶ Spec (.of R)) (a : T ⟶ Spec (.of S))
    (hj : IsFirstOrderThickening j)
    (hab : j ≫ b = a ≫ Spec.map (CommRingCat.ofHom φ)) :
    ∃! a' : T' ⟶ Spec (.of S'),
      a' ≫ Spec.map (CommRingCat.ofHom (algebraMap R S')) = b ∧
      j ≫ a' = a ≫ Spec.map (CommRingCat.ofHom π.toRingHom) := by
  have : IsClosedImmersion j := hj.1
  let A := Γ(T', ⊤)
  let q : A →+* Γ(T, ⊤) := j.appTop.hom
  have hq : Function.Surjective q := j.app_surjective ⊤ (isAffineOpen_top T')
  let I := RingHom.ker q
  have hI : I ^ 2 = ⊥ := by
    simpa only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply,
      Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] using
      congrArg (fun J => J.ideal ⟨⊤, isAffineOpen_top T'⟩) hj.2
  let β := specRingHom b
  let : Algebra R A := β.toAlgebra
  let α := specRingHom a
  have hα : α.comp (algebraMap R S) = q.comp β := by
    rw [hφ]
    have hh := congrArg specRingHom hab.symm
    rw [specRingHom_spec, specRingHom_comp] at hh
    exact hh
  let e : A ⧸ I ≃+* Γ(T, ⊤) := q.quotientKerEquivOfSurjective hq
  let a₀ : S →ₐ[R] A ⧸ I :=
    { toRingHom := e.symm.toRingHom.comp α
      commutes' := fun r => by
        change e.symm (α (algebraMap R S r)) = Ideal.Quotient.mk I (β r)
        rw [show α (algebraMap R S r) = q (β r) from RingHom.congr_fun hα r,
          RingHom.quotientKerEquivOfSurjective_symm_apply] }
  obtain ⟨α', hα', huniq⟩ := hUniversal A I hI a₀
  obtain ⟨a', ha'⟩ := specRingHom_lift α'.toRingHom
  have hqα' : q.comp α'.toRingHom = α.comp π.toRingHom := by
    ext x
    have hx := congrArg e (AlgHom.congr_fun hα' x)
    change e (Ideal.Quotient.mk I (α' x)) = e (e.symm (α (π x))) at hx
    simpa only [I, e, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      RingHom.quotientKerEquivOfSurjective_apply_mk,
      RingEquiv.apply_symm_apply] using hx
  refine ⟨a', ⟨?_, ?_⟩, ?_⟩
  · apply specRingHom_injective
    rw [specRingHom_spec, ha']
    exact α'.comp_algebraMap
  · apply specRingHom_injective
    rw [specRingHom_comp, specRingHom_spec, ha']
    exact hqα'
  · intro c hc
    have hcR : (specRingHom c).comp (algebraMap R S') = β := by
      simpa only [specRingHom_spec] using congrArg specRingHom hc.1
    let γ : S' →ₐ[R] A :=
      { toRingHom := specRingHom c
        commutes' := RingHom.congr_fun hcR }
    have hcq : q.comp γ.toRingHom = α.comp π.toRingHom := by
      have hh := congrArg specRingHom hc.2
      rw [specRingHom_spec, specRingHom_comp] at hh
      exact hh
    have hγ : (Ideal.Quotient.mkₐ R I).comp γ = a₀.comp π := by
      ext x
      apply e.injective
      change e (Ideal.Quotient.mk I (γ x)) = e (e.symm (α (π x)))
      rw [RingEquiv.apply_symm_apply]
      exact (RingHom.quotientKerEquivOfSurjective_apply_mk hq _).trans
        (RingHom.congr_fun hcq x)
    apply specRingHom_injective
    rw [ha']
    exact congrArg AlgHom.toRingHom (huniq γ hγ)

/-- The spectrum of a universal square-zero extension of `R`-algebras is a universal
first order thickening over `Spec R`, including tests by non-affine schemes.
Source: Stacks Project, More on Morphisms, proof of Lemma 04F3, third paragraph
(blueprint: lem-weil-pbc-universal-thickening-affine-case).

Proof:
1. Use the bijection between maps `Y → Spec B` and ring maps `B → Γ(Y)`
   (lem-weil-pbc-morphism-into-affine-scheme). Its compatibility with composition and
   Spec maps follows from functoriality and lem-weil-pbc-spec-map-global-sections.
2. The algebra structure maps commute with `π`, so the triangle of spectra commutes.
   Surjectivity of `π` gives a closed immersion by
   lem-weil-pbc-closed-immersion-affine-cover-criterion. Its ideal sheaf on the whole
   affine target corresponds to the kernel of `π`; powers are computed on affine opens
   (def-sbc-closed-immersion-ideal-sheaf, def-sbc-ideal-sheaf-powers). Thus its square
   is zero, and it is a first order thickening (def-sbc-first-order-thickening).
3. For affine `T'`, the closed immersion `T → T'` gives a surjection on global sections
   with square-zero kernel. Identify its quotient with `Γ(T)`. Under the bijection in
   step 1, the two required conditions on a lift are precisely that it is an `R`-algebra
   map and that its composite with the quotient map is `a.comp π`. The ring universal
   property therefore gives exactly one scheme lift.
4. Pull back an arbitrary test thickening along the affine cover and its overlaps.
   Closed immersions are stable under Limits.pullback. The kernel ideal on each affine open
   is transported along the open immersion's sections isomorphism, so its square
   remains zero (lem-weil-pbc-thickening-open-restriction). The pullback squares give
   the triangle identities for restricted solutions.
5. Cover `T'` by affine opens (lem-weil-pbc-affine-opens-basis). Step 3 gives local lifts.
   On overlaps these agree on every affine open by uniqueness. Scheme morphism gluing
   (lem-weil-pbc-scheme-morphism-gluing) gives a global lift. Both triangle identities
   hold locally, hence globally; any other lift agrees locally and hence globally.
6. Steps 2 and 5 are exactly def-weil-pbc-universal-first-order-thickening. -/
theorem isUniversalFirstOrderThickening_spec
    (R S S' : Type u) [CommRing R] [CommRing S] [CommRing S']
    (φ : R →+* S)
    [Algebra R S] [Algebra R S'] (π : S' →ₐ[R] S)
    (hφ : algebraMap R S = φ)
    (hπ : Function.Surjective π) (hK : RingHom.ker π.toRingHom ^ 2 = ⊥)
    (hUniversal : ∀ (A : Type u) [CommRing A] [Algebra R A] (I : Ideal A),
      I ^ 2 = ⊥ → ∀ a : S →ₐ[R] A ⧸ I,
        ∃! a' : S' →ₐ[R] A, (Ideal.Quotient.mkₐ R I).comp a' = a.comp π) :
    IsUniversalFirstOrderThickening
      (Spec.map (CommRingCat.ofHom φ))
      (Spec.map (CommRingCat.ofHom π.toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R S'))) := by
  have hi : IsClosedImmersion (Spec.map (CommRingCat.ofHom π.toRingHom)) :=
    IsClosedImmersion.spec_of_surjective _ hπ
  have hsquare : (Spec.map (CommRingCat.ofHom π.toRingHom)).ker ^ 2 = ⊥ := by
    apply Scheme.IdealSheafData.ext_of_isAffine
    simp only [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, Scheme.Hom.ker_apply,
      Scheme.IdealSheafData.ideal_bot]
    change RingHom.ker (Spec.map (CommRingCat.ofHom π.toRingHom)).appTop.hom ^ 2 = ⊥
    have heq : RingHom.ker
        (Spec.map (CommRingCat.ofHom π.toRingHom)).appTop.hom =
        (RingHom.ker π.toRingHom).comap (Scheme.ΓSpecIso (.of S')).hom.hom := by
      rw [← RingHom.ker_equiv_comp _
        (Scheme.ΓSpecIso (.of S)).commRingCatIsoToRingEquiv]
      rw [RingEquiv.toRingHom_eq_coe, Iso.commRingCatIsoToRingEquiv_toRingHom,
        ← CommRingCat.hom_comp, Scheme.ΓSpecIso_naturality,
        CommRingCat.hom_comp, RingHom.comap_ker]
      rfl
    rw [heq]
    apply le_bot_iff.mp
    exact (Ideal.le_comap_pow _ _).trans (by
      rw [hK]
      exact (Ideal.comap_bot_of_injective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of S')).hom).1).le)
  refine ⟨⟨hi, hsquare⟩, ?_, ?_⟩
  · rw [← Spec.map_comp]
    congr 1
    apply CommRingCat.hom_ext
    exact π.comp_algebraMap.trans hφ
  · exact lifts_of_affine_tests _ _ _
      (fun j b a hj hab => affine_lift R S S' φ π hφ hUniversal j b a hj hab)

end AlgebraicGeometry
