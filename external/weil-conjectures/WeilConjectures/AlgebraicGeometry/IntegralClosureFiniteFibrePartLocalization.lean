/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import WeilConjectures.AlgebraicGeometry.IntegralClosureFiniteFibreChooseG
import WeilConjectures.AlgebraicGeometry.IntegralClosureFiniteFibreImageClopen
import WeilConjectures.RingTheory.FiniteQuotientComponentQuasiFinite
import Mathlib.RingTheory.ZariskisMainTheorem

/-!
# Integral-closure localization of a finite fibre component

Source: Stacks Project, `more-algebra.tex`, Lemma 09XH;
blueprint: `lem-weil-pbc-integral-closure-finite-fibre-part-localization`.
-/

@[expose] public section

universe u v w z

-- Glue the principal localization isomorphisms over their union.
private theorem exists_isIso_neighborhood_of_awayMap_bijective
    {R S : Type v} [CommRing R] [CommRing S] (f : R →+* S)
    (T : Set (PrimeSpectrum S))
    (h : ∀ p ∈ T, ∃ r : R, f r ∉ p.asIdeal ∧
      Function.Bijective (Localization.awayMap f r)) :
    ∃ U : (AlgebraicGeometry.Spec (.of R)).Opens,
      T ⊆ (PrimeSpectrum.comap f) ⁻¹' U.1 ∧
      CategoryTheory.IsIso (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f) ∣_ U) := by
  classical
  choose r hr hb using fun p : T ↦ h p.1 p.2
  let V : T → (AlgebraicGeometry.Spec (.of R)).Opens := fun p ↦ PrimeSpectrum.basicOpen (r p)
  have hV : ∀ p,
      CategoryTheory.IsIso (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f) ∣_ V p) := by
    intro p
    apply (CategoryTheory.MorphismProperty.arrow_mk_iso_iff (.isomorphisms _)
      (AlgebraicGeometry.SpecMapRestrictBasicOpenIso (CommRingCat.ofHom f) (r p))).mpr
    exact (AlgebraicGeometry.isIso_SpecMap_iff).mpr (hb p)
  let 𝒰 := AlgebraicGeometry.Scheme.Opens.iSupOpenCover V
  have hU :
      CategoryTheory.IsIso (AlgebraicGeometry.Spec.map (CommRingCat.ofHom f) ∣_ ⨆ p, V p) := by
    refine (AlgebraicGeometry.IsZariskiLocalAtTarget.iff_of_openCover (P := .isomorphisms _) 𝒰).mpr
      fun p ↦ ?_
    refine (CategoryTheory.MorphismProperty.arrow_mk_iso_iff (.isomorphisms _)
      ((AlgebraicGeometry.morphismRestrictRestrict ..).symm ≪≫
        AlgebraicGeometry.morphismRestrictOpensRange ..)).mp ?_
    have : (AlgebraicGeometry.Scheme.Hom.opensFunctor
        (AlgebraicGeometry.Scheme.Opens.ι _)).obj (𝒰.f p).opensRange = V p := by
      simp only [AlgebraicGeometry.Scheme.Opens.iSupOpenCover, 𝒰,
        ← AlgebraicGeometry.Scheme.Hom.opensRange_comp,
        AlgebraicGeometry.Scheme.homOfLE_ι, AlgebraicGeometry.Scheme.Opens.opensRange_ι]
    convert! hV p
  refine ⟨⨆ p, V p, ?_, hU⟩
  intro p hp
  change PrimeSpectrum.comap f p ∈ (⨆ p, V p : (AlgebraicGeometry.Spec (.of R)).Opens)
  exact (le_iSup V ⟨p, hp⟩) (hr ⟨p, hp⟩)

/-- The finite component of a fibre of a finite-type algebra is obtained from the
integral closure, and the two algebras agree after inverting one element.

Source: Stacks Project, `more-algebra.tex`, Lemma 09XH;
(blueprint: lem-weil-pbc-integral-closure-finite-fibre-part-localization).
Proof:
1. The finite A/I-algebra C₁ makes A → B quasi-finite at each prime of
   T = Spec C₁, by lem-weil-pbc-integral-closure-finite-fibre-quasi-finite.
2. At each such prime affine Zariski Main gives an element of B' whose
   localization map is an isomorphism. Their principal opens form U, containing
   T in its inverse image, by lem-weil-pbc-integral-closure-zariski-main-away.
3. The image of T is open in the closed fibre using the isomorphism over U,
   and closed by finiteness. Its clopen decomposition yields ε', preservation
   of both factors, and the first-factor isomorphism, by
   lem-weil-pbc-integral-closure-finite-fibre-image-clopen.
4. Separate the two closed factors and the complement of U to choose g lifting
   ε' with D(g) contained in U. The comparison of local rings gives bijectivity
   of the induced localization map, by lem-weil-pbc-integral-closure-finite-fibre-choose-g.
5. The product idempotent identifies the first ideal with C₁ via q and e:
   every c has exactly one preimage fixed by ε'. The complementary ideal maps
   to C₂, giving precisely the requested compatible decomposition.
-/
theorem integralClosure_finiteFibrePart_localization
    (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B]
    (I : Ideal A)
    (C₁ : Type w) (C₂ : Type z) [CommRing C₁] [CommRing C₂]
    [Algebra (A ⧸ I) C₁] [Algebra (A ⧸ I) C₂]
    [Module.Finite (A ⧸ I) C₁]
    (e : (B ⧸ Ideal.map (algebraMap A B) I) ≃+* (C₁ × C₂))
    (he : ∀ a : A, e (Ideal.Quotient.mk _ (algebraMap A B a)) =
      (algebraMap (A ⧸ I) C₁ (Ideal.Quotient.mk I a),
       algebraMap (A ⧸ I) C₂ (Ideal.Quotient.mk I a)))
    (ε : B ⧸ Ideal.map (algebraMap A B) I)
    (hε : e ε = (1, 0)) :
    ∃ (ε' : (integralClosure A B) ⧸
          Ideal.map (algebraMap A (integralClosure A B)) I)
      (g : integralClosure A B)
      (q : (integralClosure A B) ⧸
          Ideal.map (algebraMap A (integralClosure A B)) I →+*
          (B ⧸ Ideal.map (algebraMap A B) I)),
      (∀ x : integralClosure A B,
        q (Ideal.Quotient.mk _ x) = Ideal.Quotient.mk _ x.1) ∧
      IsIdempotentElem ε' ∧ q ε' = ε ∧
      (∀ x, ε' * x = x → (e (q x)).2 = 0) ∧
      (∀ x, (1 - ε') * x = x → (e (q x)).1 = 0) ∧
      (∀ c : C₁, ∃! x, ε' * x = x ∧ e (q x) = (c, 0)) ∧
      Ideal.Quotient.mk _ g = ε' ∧
      Function.Bijective (Localization.awayMap (integralClosure A B).val.toRingHom g) := by
  classical
  have hcompat : ∀ a : A, algebraMap (A ⧸ I) C₁ (Ideal.Quotient.mk I a) =
      (e (Ideal.Quotient.mk _ (algebraMap A B a))).1 := by
    intro a
    exact (congrArg Prod.fst (he a)).symm
  let π := Ideal.Quotient.mk (Ideal.map (algebraMap A B) I)
  let π' := Ideal.Quotient.mk (Ideal.map (algebraMap A (integralClosure A B)) I)
  let ι := algebraMap (integralClosure A B) B
  let β := (RingHom.fst C₁ C₂).comp (e.toRingHom.comp π)
  let T := Set.range (PrimeSpectrum.comap β)
  have hqf := Algebra.isQuasiFiniteAtPrime_of_finite_quotient_component
    A B I C₁ C₂ e hcompat
  obtain ⟨U, hTU, hIso⟩ := exists_isIso_neighborhood_of_awayMap_bijective ι T (by
    intro p hp
    have : Algebra.QuasiFiniteAt A p.asIdeal := by
      let e := PrimeSpectrum.preimageHomeomorphFiber A B (p.comap (algebraMap A B))
      apply Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber p
      rw [← e.isOpen_image, Set.image_singleton]
      exact hqf p hp
    exact Algebra.ZariskisMainProperty.of_finiteType p.asIdeal)
  obtain ⟨q, hq, _, _, ε', hε', himage, _, hmap,
      C₁', C₂', inst₁, inst₂, e', f₁, f₂, he', hprod⟩ :=
    AlgebraicGeometry.integralClosure_finiteFibre_image_clopen I e hcompat U hIso hTU
  let := inst₁
  let := inst₂
  -- The product factors inherit their base algebra structures from the quotient.
  let a' : (A ⧸ I) →+*
      ((integralClosure A B) ⧸ Ideal.map (algebraMap A (integralClosure A B)) I) :=
    Ideal.quotientMap _ (algebraMap A (integralClosure A B)) Ideal.le_comap_map
  let : Algebra (A ⧸ I) C₁' :=
    ((RingHom.fst C₁' C₂').comp (e'.toRingHom.comp a')).toAlgebra
  let : Algebra (A ⧸ I) C₂' :=
    ((RingHom.snd C₁' C₂').comp (e'.toRingHom.comp a')).toAlgebra
  have hbase (a : A) :
      e (q (π' (algebraMap A (integralClosure A B) a))) =
        algebraMap (A ⧸ I) (C₁ × C₂) (Ideal.Quotient.mk I a) := by
    rw [hq]
    exact he a
  let f₁a : C₁' →ₐ[A ⧸ I] C₁ :=
    { f₁.toRingHom with
      commutes' := by
        intro a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact (congrArg Prod.fst ((hprod _).symm.trans (hbase a))) }
  let f₂a : C₂' →ₐ[A ⧸ I] C₂ :=
    { f₂ with
      commutes' := by
        intro a
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective a
        exact (congrArg Prod.snd ((hprod _).symm.trans (hbase a))) }
  have hU : ∀ p : PrimeSpectrum C₁',
      (PrimeSpectrum.comap π'
        (PrimeSpectrum.comap ((RingHom.fst C₁' C₂').comp e'.toRingHom) p) :
        PrimeSpectrum (integralClosure A B)) ∈ U := by
    intro p
    have hp : PrimeSpectrum.comap ((RingHom.fst C₁' C₂').comp e'.toRingHom) p ∈
        PrimeSpectrum.basicOpen ε' := by
      change (e' ε').1 ∉ p.asIdeal
      rw [he']
      exact p.isPrime.one_notMem
    have hpimage : PrimeSpectrum.comap π'
        (PrimeSpectrum.comap ((RingHom.fst C₁' C₂').comp e'.toRingHom) p) ∈
        PrimeSpectrum.comap ι '' T := by
      rw [himage]
      exact ⟨_, hp, rfl⟩
    obtain ⟨x, hx, hxp⟩ := hpimage
    exact hxp ▸ hTU hx
  obtain ⟨g, hg, _, hbij⟩ := integralClosure.exists_bijective_awayMap_of_isIso_restrict
    A B C₁ C₂ C₁' C₂' I e e' he (fun _ ↦ rfl) f₁a f₂a
    (fun b ↦ (hq b ▸ hprod (π' b))) U hU hIso
  refine ⟨ε', g, q, hq, hε', ?_, ?_, ?_, ?_, ?_, hbij⟩
  · exact hmap.trans (e.injective (by simpa using hε.symm))
  · intro x hx
    have hx' := congrArg (fun y ↦ (e' y).2) hx
    have hxzero : (e' x).2 = 0 := by simpa [map_mul, he'] using hx'.symm
    rw [hprod, hxzero, map_zero]
  · intro x hx
    have hx' := congrArg (fun y ↦ (e' y).1) hx
    have hxzero : (e' x).1 = 0 := by simpa [map_mul, map_sub, he'] using hx'.symm
    rw [hprod, hxzero, map_zero]
  · intro c
    refine ⟨e'.symm (f₁.symm c, 0), ⟨?_, ?_⟩, ?_⟩
    · apply e'.injective
      simp [map_mul, he']
    · rw [hprod]
      simp
    · intro x hx
      apply e'.injective
      apply Prod.ext
      · apply f₁.injective
        simpa [hprod] using congrArg Prod.fst hx.2
      · have hx' := congrArg (fun y ↦ (e' y).2) hx.1
        simpa [map_mul, he'] using hx'.symm
  · simpa only [← he', e'.symm_apply_apply] using hg
