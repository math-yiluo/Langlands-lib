/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
import WeilConjectures.AlgebraicGeometry.QuotientFirstFactorImageOpen
import WeilConjectures.AlgebraicGeometry.QuotientFirstFactorIso

/-! # The finite fibre component has a clopen image in the integral closure

Source: literature/stacks-project/more-algebra.tex:2529-2541, proof of Lemma Tag 09XH
(blueprint: lem-weil-pbc-integral-closure-finite-fibre-image-clopen)
-/

@[expose] public section

universe u v w z

open AlgebraicGeometry CategoryTheory

namespace AlgebraicGeometry

/-- The finite fibre component has a clopen image in the integral closure.

Source: literature/stacks-project/more-algebra.tex:2529-2541, proof of Lemma Tag 09XH
(blueprint: lem-weil-pbc-integral-closure-finite-fibre-image-clopen).

1. For a lift of the component idempotent, identify `T` with `V(IB) ∩ D(ε)` using
   lem-weil-pbc-spec-quotient-homeomorphism-zero-locus.
2. The inclusion carries `IB'` into `IB`, and the image of `I` generates both ideals;
   consequently the inverse image of `V(IB')` is `V(IB)`.
3. The isomorphism over `U` carries the principal open piece to an open piece, showing
   that the image of `T` is open in `V(IB')` (def-weil-affine-spectrum).
4. Finiteness of `C₁` over `A/I` gives integrality over `B'`, so the spectrum image is
   closed by lem-weil-pbc-finite-algebra-is-integral and lem-weil-pbc-integral-spec-closed-map.
5. Pull back along the quotient-spectrum homeomorphism and apply
   lem-weil-pbc-spec-clopen-idempotent to obtain the unique idempotent and product factors.
6. Injectivity over `U` shows that the inverse image of the image is precisely `T`.
7. The two idempotents have the same basic open after pullback. Uniqueness in
   lem-weil-pbc-spec-clopen-idempotent gives `f ε' = ε` and preservation of both factors.
8. Use lem-weil-pbc-spec-basic-opens-unit-ideal-quasi-compact to choose a lift `g` of `ε'`
   with `D(g) ⊆ U`, by separating the closed complement of `U` from the first factor.
9. On `D(g)` the isomorphism of locally ringed spaces identifies the section rings,
   hence the localizations `B'_g` and `B_g` (lem-weil-pbc-morphism-into-affine-scheme,
   lem-weil-pbc-affine-ideals-closed-subscheme, def-weil-ring-localization-away).
10. Quotient this localization isomorphism by the corresponding ideals `(I, 1-g)`;
    these quotient rings are the first factors, and the induced first-factor map is
    therefore a ring isomorphism. -/
theorem integralClosure_finiteFibre_image_clopen
    {A : Type v} {B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B] (I : Ideal A)
    {C₁ : Type w} {C₂ : Type z} [CommRing C₁] [CommRing C₂]
    [Algebra (A ⧸ I) C₁] [Module.Finite (A ⧸ I) C₁]
    (e : (B ⧸ Ideal.map (algebraMap A B) I) ≃+* C₁ × C₂)
    (hcompat : ∀ a : A, algebraMap (A ⧸ I) C₁ (Ideal.Quotient.mk I a) =
      (e (Ideal.Quotient.mk _ (algebraMap A B a))).1)
    (U : (Spec (.of (integralClosure A B))).Opens)
    (hiso : IsIso (Spec.map (CommRingCat.ofHom
      (algebraMap (integralClosure A B) B)) ∣_ U)) :
    let R := B ⧸ Ideal.map (algebraMap A B) I
    let R' := (integralClosure A B) ⧸ Ideal.map (algebraMap A (integralClosure A B)) I
    let π := Ideal.Quotient.mk (Ideal.map (algebraMap A B) I)
    let π' := Ideal.Quotient.mk (Ideal.map (algebraMap A (integralClosure A B)) I)
    let ι := algebraMap (integralClosure A B) B
    let φ := PrimeSpectrum.comap ι
    let β := (RingHom.fst C₁ C₂).comp (e.toRingHom.comp π)
    let T := Set.range (PrimeSpectrum.comap β)
    T ⊆ φ ⁻¹' U.1 →
      ∃ (f : R' →+* R),
        (∀ b, f (π' b) = π (ι b)) ∧
        IsClopen ((PrimeSpectrum.comap π') ⁻¹' (φ '' T)) ∧
        φ ⁻¹' (φ '' T) = T ∧
        ∃ (ε' : R'), IsIdempotentElem ε' ∧
          φ '' T = PrimeSpectrum.comap π' '' (PrimeSpectrum.basicOpen ε' : Set _) ∧
          (∀ δ : R', IsIdempotentElem δ →
            φ '' T = PrimeSpectrum.comap π' '' (PrimeSpectrum.basicOpen δ : Set _) →
            δ = ε') ∧
          f ε' = e.symm (1, 0) ∧
          ∃ (C'₁ C'₂ : Type u) (_ : CommRing C'₁) (_ : CommRing C'₂)
            (e' : R' ≃+* C'₁ × C'₂) (g : C'₁ ≃+* C₁) (h : C'₂ →+* C₂),
            e' ε' = (1, 0) ∧
            ∀ r : R', e (f r) = (g (e' r).1, h (e' r).2) := by
  classical
  dsimp only
  intro hT
  let J := Ideal.map (algebraMap A B) I
  let J' := Ideal.map (algebraMap A (integralClosure A B)) I
  let π := Ideal.Quotient.mk J
  let π' := Ideal.Quotient.mk J'
  let ι := algebraMap (integralClosure A B) B
  let φ := PrimeSpectrum.comap ι
  let β := (RingHom.fst C₁ C₂).comp (e.toRingHom.comp π)
  let T := Set.range (PrimeSpectrum.comap β)
  have hJ : Ideal.map ι J' = J := by
    rw [Ideal.map_map, ← IsScalarTower.algebraMap_eq]
  let f : (integralClosure A B ⧸ J') →+* (B ⧸ J) :=
    Ideal.Quotient.lift J' (π.comp ι) (by
      intro b hb
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← hJ]
      exact Ideal.mem_map_of_mem ι hb)
  have hf : ∀ b, f (π' b) = π (ι b) := fun _ ↦ rfl
  have hcomm : π.comp ι = f.comp π' := by ext b; rfl
  have hclosed : IsClosed (φ '' T) := by
    have hint : (β.comp ι).IsIntegral := by
      apply RingHom.IsIntegral.tower_top (algebraMap A (integralClosure A B))
      have heq : (β.comp ι).comp (algebraMap A (integralClosure A B)) =
          (algebraMap (A ⧸ I) C₁).comp (Ideal.Quotient.mk I) := by
        ext a
        simpa [β, π, ι, J, ← IsScalarTower.algebraMap_apply] using (hcompat a).symm
      rw [heq]
      exact (RingHom.isIntegral_of_surjective (Ideal.Quotient.mk I)
        Ideal.Quotient.mk_surjective).trans _ _ (Algebra.IsIntegral.isIntegral (R := A ⧸ I))
    have hmap := PrimeSpectrum.isClosedMap_comap_of_isIntegral (β.comp ι) hint
    have hrange : φ '' T = Set.range (PrimeSpectrum.comap (β.comp ι)) := by
      rw [PrimeSpectrum.comap_comp, Set.range_comp]
    rw [hrange]
    simpa only [Set.image_univ] using hmap Set.univ isClosed_univ
  have hopen := quotient_firstFactor_image_isOpen ι J' J hJ e U hiso hT
  have hclopen : IsClopen ((PrimeSpectrum.comap π') ⁻¹' (φ '' T)) :=
    ⟨hclosed.preimage (PrimeSpectrum.continuous_comap π'), hopen⟩
  have hpre : φ ⁻¹' (φ '' T) = T := by
    ext q
    constructor
    · rintro ⟨t, ht, heq⟩
      have hq : φ q ∈ U.1 := heq ▸ hT ht
      let qU : (Spec.map (CommRingCat.ofHom ι) ⁻¹ᵁ U).toScheme := ⟨q, hq⟩
      let tU : (Spec.map (CommRingCat.ofHom ι) ⁻¹ᵁ U).toScheme := ⟨t, hT ht⟩
      have hqt : qU = tU := (Scheme.Hom.homeomorph
        (Spec.map (CommRingCat.ofHom ι) ∣_ U)).injective (by
          apply Subtype.ext
          simpa [qU, tU, Scheme.Hom.homeomorph_apply, morphismRestrict_base_coe,
            Spec.map_apply, φ] using
            heq.symm)
      have : q = t := congrArg Subtype.val hqt
      exact this ▸ ht
    · intro ht
      exact ⟨q, ht, rfl⟩
  obtain ⟨c, ⟨hc, hbasic⟩, huniq⟩ :=
    PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen hclopen
  have hsubset : φ '' T ⊆ Set.range (PrimeSpectrum.comap π') := by
    rintro _ ⟨t, ⟨p, rfl⟩, rfl⟩
    rw [range_comap_of_surjective _ π' Ideal.Quotient.mk_surjective]
    rw [Ideal.mk_ker]
    intro b hb
    change ι b ∈ (PrimeSpectrum.comap β p).asIdeal
    change β (ι b) ∈ p.asIdeal
    have hz : π (ι b) = 0 := by
      apply Ideal.Quotient.eq_zero_iff_mem.mpr
      rw [← hJ]
      exact Ideal.mem_map_of_mem ι hb
    change (e (π (ι b))).1 ∈ p.asIdeal
    rw [hz, map_zero]
    exact p.asIdeal.zero_mem
  have himage : φ '' T = PrimeSpectrum.comap π' ''
      (PrimeSpectrum.basicOpen c : Set _) := by
    rw [← hbasic]
    symm
    rw [Set.image_preimage_eq_inter_range, Set.inter_eq_left.mpr hsubset]
  have hfc : f c = e.symm (1, 0) := by
    apply PrimeSpectrum.basicOpen_injOn_isIdempotentElem (hc.map f)
      (by
        have hid : IsIdempotentElem ((1, 0) : C₁ × C₂) := by
          ext <;> simp
        exact hid.map e.symm)
    apply SetLike.ext'
    have htquot : (PrimeSpectrum.comap π) ⁻¹' T =
        (PrimeSpectrum.basicOpen (e.symm (1, 0)) : Set _) := by
      have ht : T = PrimeSpectrum.comap π ''
          (PrimeSpectrum.basicOpen (e.symm (1, 0)) : Set _) := by
        change Set.range (PrimeSpectrum.comap
          (((RingHom.fst C₁ C₂).comp e.toRingHom).comp π)) = _
        rw [PrimeSpectrum.comap_comp, Set.range_comp, firstFactor_range e]
      rw [ht]
      exact Set.preimage_image_eq _
        (PrimeSpectrum.comap_injective_of_surjective π Ideal.Quotient.mk_surjective)
    have hcomap : PrimeSpectrum.comap π' ∘ PrimeSpectrum.comap f =
        φ ∘ PrimeSpectrum.comap π := by
      rw [← PrimeSpectrum.comap_comp, ← hcomm, PrimeSpectrum.comap_comp]
    calc
      (PrimeSpectrum.basicOpen (f c) : Set _) =
          (PrimeSpectrum.comap f) ⁻¹' (PrimeSpectrum.basicOpen c : Set _) := rfl
      _ = (PrimeSpectrum.comap f) ⁻¹' ((PrimeSpectrum.comap π') ⁻¹' (φ '' T)) :=
        congrArg _ hbasic.symm
      _ = (PrimeSpectrum.comap π) ⁻¹' (φ ⁻¹' (φ '' T)) := by
        rw [← Set.preimage_comp, hcomap, Set.preimage_comp]
      _ = (PrimeSpectrum.basicOpen (e.symm (1, 0)) : Set _) := by rw [hpre, htquot]
  refine ⟨f, hf, hclopen, hpre, c, hc, himage, ?_, hfc, ?_⟩
  · intro δ hδ hδimage
    apply huniq δ
    refine ⟨hδ, ?_⟩
    rw [hδimage]
    exact Set.preimage_image_eq _
      (PrimeSpectrum.comap_injective_of_surjective π' Ideal.Quotient.mk_surjective)
  · apply quotient_firstFactor_equiv_of_restrict_iso ι J' J hJ f hf e c hc hfc U hiso
    rw [← himage]
    rintro _ ⟨t, ht, rfl⟩
    exact hT ht

end AlgebraicGeometry
