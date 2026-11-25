/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict

import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.RingTheory.Idempotents

/-! # Identification of a quotient factor over an isomorphism locus

Source: Stacks Project, More on Algebra, proof of Tag 09XH.
(blueprint: lem-weil-pbc-quotient-first-factor-iso)
-/

@[expose] public section

universe u w z

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

private theorem factor_bijective_of_away_bijective
    {R S A B : Type*} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    (i : R →+* S) (qR : R →+* A) (qS : S →+* B) (a : A →+* B)
    (hqR : Function.Surjective qR) (hqS : Function.Surjective qS)
    (ha : ∀ r, a (qR r) = qS (i r))
    (hker : Ideal.map i (RingHom.ker qR) = RingHom.ker qS)
    (g : R) (hg : qR g = 1) (hbij : Function.Bijective (Localization.awayMap i g)) :
    Function.Bijective a := by
  classical
  let e := RingEquiv.ofBijective (Localization.awayMap i g) hbij
  let lR : Localization.Away g →+* A :=
    IsLocalization.Away.lift g (hg.symm ▸ isUnit_one)
  have hgS : qS (i g) = 1 := (ha g).symm.trans (by rw [hg, map_one])
  let lS : Localization.Away (i g) →+* B :=
    IsLocalization.Away.lift (i g) (hgS.symm ▸ isUnit_one)
  have he (r : R) : e (algebraMap R (Localization.Away g) r) =
      algebraMap S (Localization.Away (i g)) (i r) := by
    change Localization.awayMap i g (algebraMap R (Localization.Away g) r) = _
    exact IsLocalization.map_eq _ _
  have hlR (r : R) : lR (algebraMap R (Localization.Away g) r) = qR r :=
    IsLocalization.Away.lift_eq _ _ _
  have hlS (r : S) : lS (algebraMap S (Localization.Away (i g)) r) = qS r :=
    IsLocalization.Away.lift_eq _ _ _
  let b : S →+* A := lR.comp (e.symm.toRingHom.comp
    (algebraMap S (Localization.Away (i g))))
  have hb (r : R) : b (i r) = qR r := by
    change lR (e.symm (algebraMap S (Localization.Away (i g)) (i r))) = _
    rw [← he, e.symm_apply_apply, hlR]
  have hkill : RingHom.ker qS ≤ RingHom.ker b := by
    rw [← hker, Ideal.map_le_iff_le_comap]
    intro r hr
    change b (i r) = 0
    rw [hb]
    exact hr
  let inv : B →+* A := RingHom.liftOfSurjective qS hqS ⟨b, hkill⟩
  have hinv (s : S) : inv (qS s) = b s := RingHom.liftOfSurjective_comp_apply _ _ _ _
  have hloc : a.comp lR = lS.comp e.toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers g)
    ext r
    change a (lR (algebraMap R (Localization.Away g) r)) =
      lS (e (algebraMap R (Localization.Away g) r))
    rw [hlR, he, hlS, ha]
  have hab (s : S) : a (b s) = qS s := by
    change a (lR (e.symm (algebraMap S (Localization.Away (i g)) s))) = _
    have hh := DFunLike.congr_fun hloc (e.symm (algebraMap S (Localization.Away (i g)) s))
    change a (lR (e.symm (algebraMap S (Localization.Away (i g)) s))) =
      lS (e (e.symm (algebraMap S (Localization.Away (i g)) s))) at hh
    rwa [e.apply_symm_apply, hlS] at hh
  refine ⟨Function.LeftInverse.injective (g := inv) ?_, ?_⟩
  · intro x
    obtain ⟨r, rfl⟩ := hqR x
    rw [ha, hinv, hb]
  · intro y
    obtain ⟨s, rfl⟩ := hqS y
    exact ⟨inv (qS s), by rw [hinv, hab]⟩

private theorem ker_comp_quotient_mk
    {R A : Type*} [CommRing R] [CommRing A] (J : Ideal R)
    (p : (R ⧸ J) →+* A) (g : R)
    (hp : RingHom.ker p = Ideal.span {1 - Ideal.Quotient.mk J g}) :
    RingHom.ker (p.comp (Ideal.Quotient.mk J)) = J ⊔ Ideal.span {1 - g} := by
  rw [← RingHom.comap_ker, hp]
  have hm : Ideal.span {1 - Ideal.Quotient.mk J g} =
      Ideal.map (Ideal.Quotient.mk J) (Ideal.span {1 - g}) := by
    rw [Ideal.map_span, Set.image_singleton, map_sub, map_one]
  rw [hm, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
    ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
  exact sup_comm _ _

/-- An idempotent factor supported in the isomorphism locus is preserved isomorphically.

Source: literature/stacks-project/more-algebra.tex:2529-2541, proof of Tag 09XH,
including the localization and final quotient argument.
(blueprint: lem-weil-pbc-quotient-first-factor-iso).

Split S'/J' by the idempotent c as C'₁ = (S'/J')/(1-c) and C'₂ = (S'/J')/(c),
using the Chinese remainder theorem. The equality f(c)=e.symm(1,0) makes f diagonal
on these products and gives ring maps to D₁ and D₂. It remains to prove that the
first map is an isomorphism. Let t lift c and K'=J'+(1-t). Its zero locus is the
first factor and is contained in U. Write the complement of U as V(L). Since
V(L) and V(K') are disjoint, L+K'=S'; choose 1=l+k with l in L and k in K'.
Put g=t*l. Idempotence gives g-t in J', and g in L gives D(g) contained in U.
The scheme isomorphism on U identifies the section rings on D(g), which are the
localizations S'_g and S_{i(g)}, with the canonical localization map induced by i.
Quotient this ring isomorphism by the extensions of K'=J'+(1-g) and
K=J+(1-i(g)). These ideals correspond because J=map i J'. Since g becomes 1
in each quotient, the localization quotients are S'/K' and S/K respectively.
These are precisely C'₁ and D₁, and the resulting isomorphism is the first map.
In Lean this quotient transport is implemented by extending the quotient maps to
localizations (g maps to 1), composing with the inverse localization isomorphism,
and descending along the surjective first-factor map. Kernel compatibility makes
this descent well-defined; uniqueness of localization lifts proves the two inverse
identities. The second factor map is the map already induced by f. -/
theorem quotient_firstFactor_equiv_of_restrict_iso
    {S' S : Type u} [CommRing S'] [CommRing S] (i : S' →+* S)
    (J' : Ideal S') (J : Ideal S) (hJ : Ideal.map i J' = J)
    (f : (S' ⧸ J') →+* (S ⧸ J))
    (hf : ∀ b, f (Ideal.Quotient.mk J' b) = Ideal.Quotient.mk J (i b))
    {D₁ : Type w} {D₂ : Type z} [CommRing D₁] [CommRing D₂]
    (e : (S ⧸ J) ≃+* D₁ × D₂) (c : S' ⧸ J') (hc : IsIdempotentElem c)
    (hfc : f c = e.symm (1, 0)) (U : (Spec (.of S')).Opens)
    (hiso : IsIso (Spec.map (CommRingCat.ofHom i) ∣_ U))
    (hU : PrimeSpectrum.comap (Ideal.Quotient.mk J') ''
      (PrimeSpectrum.basicOpen c : Set _) ⊆ U.1) :
    ∃ (D'₁ D'₂ : Type u) (_ : CommRing D'₁) (_ : CommRing D'₂)
      (e' : (S' ⧸ J') ≃+* D'₁ × D'₂) (g : D'₁ ≃+* D₁) (h : D'₂ →+* D₂),
      e' c = (1, 0) ∧
      ∀ r : S' ⧸ J', e (f r) = (g (e' r).1, h (e' r).2) := by
  classical
  let Q := S' ⧸ J'
  let I₁ : Ideal Q := Ideal.span {1 - c}
  let I₂ : Ideal Q := Ideal.span {c}
  let D'₁ := Q ⧸ I₁
  let D'₂ := Q ⧸ I₂
  let e' : Q ≃+* D'₁ × D'₂ := RingEquiv.ofBijective
    ((Ideal.Quotient.mk I₁).prod (Ideal.Quotient.mk I₂))
    (RingHom.prod_bijective_of_isIdempotentElem hc.one_sub hc
      (sub_add_cancel 1 c) hc.one_sub_mul_self)
  have he' (r : Q) : e' r = (Ideal.Quotient.mk I₁ r, Ideal.Quotient.mk I₂ r) := rfl
  have he'c : e' c = (1, 0) := by
    rw [he']
    apply Prod.ext
    · apply sub_eq_zero.mp
      rw [← map_one (Ideal.Quotient.mk I₁), ← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (by
        simpa only [neg_sub] using
          I₁.neg_mem (Ideal.subset_span (Set.mem_singleton (1 - c))))
    · exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton c))
  let p₁ : Q →+* D₁ := (RingHom.fst D₁ D₂).comp (e.toRingHom.comp f)
  let p₂ : Q →+* D₂ := (RingHom.snd D₁ D₂).comp (e.toRingHom.comp f)
  have hp₁c : p₁ c = 1 := by
    change (e (f c)).1 = 1
    rw [hfc, e.apply_symm_apply]
  have hp₂c : p₂ c = 0 := by
    change (e (f c)).2 = 0
    rw [hfc, e.apply_symm_apply]
  let a : D'₁ →+* D₁ := Ideal.Quotient.lift I₁ p₁ (by
    intro x hx
    have hle : I₁ ≤ RingHom.ker p₁ := by
      apply Ideal.span_le.mpr
      intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      change p₁ (1 - c) = 0
      simp [hp₁c]
    exact hle hx)
  let b : D'₂ →+* D₂ := Ideal.Quotient.lift I₂ p₂ (by
    intro x hx
    have hle : I₂ ≤ RingHom.ker p₂ := by
      apply Ideal.span_le.mpr
      intro y hy
      obtain rfl := Set.mem_singleton_iff.mp hy
      exact hp₂c
    exact hle hx)
  let qR : S' →+* D'₁ := (Ideal.Quotient.mk I₁).comp (Ideal.Quotient.mk J')
  let qS : S →+* D₁ := ((RingHom.fst D₁ D₂).comp e.toRingHom).comp
    (Ideal.Quotient.mk J)
  have hqR : Function.Surjective qR :=
    Ideal.Quotient.mk_surjective.comp Ideal.Quotient.mk_surjective
  have hqS : Function.Surjective qS := by
    intro x
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (e.symm (x, 0))
    refine ⟨r, ?_⟩
    simp [qS, hr]
  have ha (r : S') : a (qR r) = qS (i r) := by
    change a (Ideal.Quotient.mk I₁ (Ideal.Quotient.mk J' r)) = _
    rw [Ideal.Quotient.lift_mk]
    change (e (f (Ideal.Quotient.mk J' r))).1 = (e (Ideal.Quotient.mk J (i r))).1
    rw [hf]
  have hex : ∃ g : S', Ideal.Quotient.mk J' g = c ∧
      PrimeSpectrum.basicOpen g ≤ U := by
    let W : TopologicalSpace.Opens (PrimeSpectrum S') := U
    let L := PrimeSpectrum.vanishingIdeal ((W : Set (PrimeSpectrum S'))ᶜ)
    have hL : PrimeSpectrum.zeroLocus (L : Set S') =
        (W : Set (PrimeSpectrum S'))ᶜ :=
      (PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure _).trans
        W.isOpen.isClosed_compl.closure_eq
    have hK : PrimeSpectrum.zeroLocus (RingHom.ker qR : Set S') ⊆
        (W : Set (PrimeSpectrum S')) := by
      rw [← range_comap_of_surjective D'₁ qR hqR]
      rintro _ ⟨p, rfl⟩
      apply hU
      refine ⟨PrimeSpectrum.comap (Ideal.Quotient.mk I₁) p, ?_, rfl⟩
      change Ideal.Quotient.mk I₁ c ∉ p.asIdeal
      have hc1 : Ideal.Quotient.mk I₁ c = 1 := congrArg Prod.fst he'c
      rw [hc1]
      exact p.isPrime.one_notMem
    have hLK : L ⊔ RingHom.ker qR = ⊤ := by
      apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
      rw [PrimeSpectrum.zeroLocus_sup, hL]
      exact Set.eq_empty_iff_forall_notMem.mpr fun p hp ↦ hp.1 (hK hp.2)
    obtain ⟨l, hl, k, hk, hlk⟩ := Submodule.mem_sup.mp
      (show (1 : S') ∈ L ⊔ RingHom.ker qR from hLK ▸ trivial)
    obtain ⟨t, ht⟩ := Ideal.Quotient.mk_surjective c
    have hk0 : Ideal.Quotient.mk I₁ (Ideal.Quotient.mk J' k) = 0 := hk
    have hkI : Ideal.Quotient.mk J' k ∈ I₁ :=
      Ideal.Quotient.eq_zero_iff_mem.mp hk0
    have hck : c * Ideal.Quotient.mk J' k = 0 := by
      obtain ⟨v, hv⟩ := Ideal.mem_span_singleton.mp hkI
      rw [hv, ← mul_assoc, hc.mul_one_sub_self, zero_mul]
    have hgl : Ideal.Quotient.mk J' (t * l) = c := by
      have heq := congrArg (fun r : S' ↦ c * Ideal.Quotient.mk J' r) hlk
      simpa only [map_add, mul_add, hck, add_zero, map_one, mul_one,
        map_mul, ht] using heq
    refine ⟨t * l, hgl, ?_⟩
    intro p hp
    by_contra hn
    have hmem : t * l ∈ L := L.mul_mem_left t hl
    exact hp ((PrimeSpectrum.mem_zeroLocus _ _).mp (hL.symm ▸ hn) hmem)
  obtain ⟨g, hg, hD⟩ := hex
  have hbij : Function.Bijective (Localization.awayMap i g) := by
    let φ := Spec.map (CommRingCat.ofHom i)
    have : IsIso (φ ∣_ U) := hiso
    let V := U.ι ⁻¹ᵁ PrimeSpectrum.basicOpen g
    have hV : U.ι ''ᵁ V = PrimeSpectrum.basicOpen g := by
      rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
      exact inf_eq_right.mpr hD
    have hrestrict : IsIso (φ ∣_ PrimeSpectrum.basicOpen g) := by
      rw [← hV]
      exact (Arrow.isIso_iff_isIso_of_isIso (morphismRestrictRestrict φ U V).hom).mp
        inferInstance
    exact isIso_SpecMap_iff.mp
      ((Arrow.isIso_iff_isIso_of_isIso
        (SpecMapRestrictBasicOpenIso (CommRingCat.ofHom i) g).hom).mp hrestrict)
  have hker : Ideal.map i (RingHom.ker qR) = RingHom.ker qS := by
    let p : (S ⧸ J) →+* D₁ := (RingHom.fst D₁ D₂).comp e.toRingHom
    have hp : RingHom.ker p = Ideal.span {1 - f c} := by
      apply le_antisymm
      · intro x hx
        apply Ideal.mem_span_singleton.mpr
        refine ⟨x, ?_⟩
        apply e.injective
        rw [map_mul, map_sub, map_one, hfc, e.apply_symm_apply]
        have hx0 : (e x).1 = 0 := hx
        apply Prod.ext
        · simp [hx0]
        · simp
      · apply Ideal.span_le.mpr
        intro x hx
        obtain rfl := Set.mem_singleton_iff.mp hx
        change (e (1 - f c)).1 = 0
        rw [map_sub, map_one, hfc, e.apply_symm_apply]
        simp
    have hR : RingHom.ker qR = J' ⊔ Ideal.span {1 - g} :=
      ker_comp_quotient_mk J' (Ideal.Quotient.mk I₁) g (by
        rw [Ideal.mk_ker, hg])
    have hS : RingHom.ker qS = J ⊔ Ideal.span {1 - i g} :=
      ker_comp_quotient_mk J p (i g) (by rw [← hf, hg]; exact hp)
    rw [hR, hS, Ideal.map_sup, hJ, Ideal.map_span, Set.image_singleton,
      map_sub, map_one]
  have hqg : qR g = 1 := by
    change Ideal.Quotient.mk I₁ (Ideal.Quotient.mk J' g) = 1
    rw [hg]
    exact congrArg Prod.fst he'c
  have habij : Function.Bijective a :=
    factor_bijective_of_away_bijective i qR qS a hqR hqS ha hker g hqg hbij
  refine ⟨D'₁, D'₂, inferInstance, inferInstance, e', RingEquiv.ofBijective a habij,
    b, he'c, ?_⟩
  intro r
  rw [he']
  apply Prod.ext <;> rfl

end AlgebraicGeometry
