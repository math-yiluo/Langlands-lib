/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselization


public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import WeilConjectures.AlgebraicGeometry.StrictHenselizationStructuralMapExtension
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Regular

import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRegularDivisorQuotient
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRootTameNormalization
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselizationStructuralFlat
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-! # A normalization model ready for purity after the group-order root extension

## References

* Stacks Project, Tags 09EB, 0BRM, 0EYG and 0EYH, through the construction of B' and tame
  normalization
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem root_pow (R : Type u) [CommRing R] (f : R) (n : ℕ) :
    AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f) ^ n =
      AdjoinRoot.of ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f) f := by
  have h := AdjoinRoot.eval₂_root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f)
  simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
    Polynomial.eval₂_C, sub_eq_zero] using h

set_option backward.isDefEq.respectTransparency false in
private noncomputable def root_quotient_equiv (R : Type u) [CommRing R]
    (f : R) (n : ℕ) (hn : 0 < n) :
    (AdjoinRoot ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f) ⧸
      Ideal.span {AdjoinRoot.root ((Polynomial.X : Polynomial R) ^ n - Polynomial.C f)}) ≃+*
      (R ⧸ Ideal.span {f}) := by
  let P := (Polynomial.X : Polynomial R) ^ n - Polynomial.C f
  let B := AdjoinRoot P
  let t := AdjoinRoot.root P
  let I := Ideal.span ({t} : Set B)
  let J := Ideal.span ({f} : Set R)
  let v := AdjoinRoot.lift (f := P) (Ideal.Quotient.mk J) 0 (by
    simp only [P, Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, zero_pow hn.ne', zero_sub, neg_eq_zero]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f))
  let g : B ⧸ I →+* R ⧸ J := Ideal.Quotient.lift I v (by
    intro y hy
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hy
    rw [map_mul]
    have hv : v t = 0 := AdjoinRoot.lift_root _
    rw [hv, zero_mul])
  let w := (Ideal.Quotient.mk I).comp (AdjoinRoot.of P)
  have hw : w f = 0 := by
    change Ideal.Quotient.mk I (AdjoinRoot.of P f) = 0
    rw [← root_pow R f n, map_pow]
    have ht : Ideal.Quotient.mk I t = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)
    change (Ideal.Quotient.mk I t) ^ n = 0
    rw [ht, zero_pow hn.ne']
  let h : R ⧸ J →+* B ⧸ I := Ideal.Quotient.lift J w (by
    intro y hy
    obtain ⟨z, rfl⟩ := Ideal.mem_span_singleton.mp hy
    rw [map_mul, hw, zero_mul])
  apply RingEquiv.ofRingHom g h
  · apply Ideal.Quotient.ringHom_ext
    ext r
    change v (AdjoinRoot.of P r) = Ideal.Quotient.mk J r
    exact AdjoinRoot.lift_of _
  · apply Ideal.Quotient.ringHom_ext
    apply AdjoinRoot.ringHom_ext
    · ext r
      change h (g (Ideal.Quotient.mk I (AdjoinRoot.of P r))) =
        Ideal.Quotient.mk I (AdjoinRoot.of P r)
      change h (v (AdjoinRoot.of P r)) = _
      rw [show v (AdjoinRoot.of P r) = Ideal.Quotient.mk J r from AdjoinRoot.lift_of _]
      rfl
    · change h (g (Ideal.Quotient.mk I t)) = Ideal.Quotient.mk I t
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self t)]
      rw [map_zero, map_zero]


/-- A finite normalization model is etale at the generic point of the root divisor. -/
theorem GaloisCover.strict_hensel_root_purity_data
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (hG : IsUnit (Nat.card G : R))
    [IsRegularRing R] (hf : IsSMulRegular R f)
    [IsRegularRing (R ⧸ Ideal.span {f})]
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    {Ω : Type u} [Field Ω] [IsAlgClosed Ω] (barY : Spec (.of Ω) ⟶ Spec R)
    (b : R ⟶ strictHenselization barY)
    (hb : Spec.map b = strictLocalizationToBase barY) :
    let H := strictHenselization barY
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ¬ IsUnit g →
    IsLocallyNoetherian N ∧
      ∃ (D : Scheme.{u}) (j : D ⟶ N),
        IsRegular D ∧ IsIntegral D ∧ IsEffectiveCartierCenter j ∧
        (∀ z : N, z ∈ V ↔ z ∉ Set.range j) ∧
        ∃ (C : Scheme.{u}) (n : C ⟶ N),
          IsFinite n ∧ Etale (n ∣_ V) ∧
          ∃ (O : N.Opens) (η : D), IsGenericPoint η Set.univ ∧
            j η ∈ O ∧ Etale (n ∣_ O) ∧
          ∃ ζ : (n ⁻¹ᵁ V).toScheme ≅
              pullback (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ),
            ζ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) =
              n ∣_ V := by
  classical
  dsimp only
  let H := strictHenselization barY
  let g := b.hom f
  let P := (Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g
  let A := AdjoinRoot P
  let t := AdjoinRoot.root P
  let I := Ideal.span ({t} : Set A)
  let N := Spec (CommRingCat.of A)
  let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
  intro hg
  obtain ⟨hH, hQ, hQD⟩ := strictHenselization_regular_divisor_quotient R f barY b hb hg
  let : IsNoetherianRing H := hH
  let : IsRegularRing (H ⧸ Ideal.span {g}) := hQ
  let : IsDomain (H ⧸ Ideal.span {g}) := hQD
  have hm : P.Monic := Polynomial.monic_X_pow_sub_C g (Nat.card_pos (α := G)).ne'
  let : Module.Finite H A := hm.finite_adjoinRoot
  let : Module.Free H A := hm.free_adjoinRoot
  have hflat := strictHenselization_structural_ringHom_flat R barY b hb
  let : Algebra R H := b.hom.toAlgebra
  let : Module.Flat R H := hflat
  have hgH : IsSMulRegular H g := hf.of_flat
  have htreg : IsSMulRegular A t := by
    apply (IsSMulRegular.pow_iff (Nat.card_pos (α := G))).mp
    rw [root_pow H g (Nat.card G)]
    exact hgH.of_flat
  have htr : _root_.IsRegular t :=
    (Commute.isRegular_iff (fun a ↦ Commute.all _ a)).mpr
      (isLeftRegular_iff.mpr htreg)
  let e := root_quotient_equiv H g (Nat.card G) (Nat.card_pos (α := G))
  let : IsRegularRing (A ⧸ I) := IsRegularRing.of_ringEquiv e.symm
  let : IsDomain (A ⧸ I) := e.toMulEquiv.isDomain_iff.mpr hQD
  let D := Spec (CommRingCat.of (A ⧸ I))
  let j : D ⟶ N := Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))
  have hD : IsRegular D := by
    constructor
    intro x
    exact IsRegularLocalRing.of_ringEquiv
      (Spec.stalkIso (CommRingCat.of (A ⧸ I)) x).commRingCatIsoToRingEquiv.symm
  have hDI : IsIntegral D := inferInstance
  have hj : IsEffectiveCartierCenter j := by
    have : IsClosedImmersion j := IsClosedImmersion.spec_of_surjective
      (CommRingCat.ofHom (Ideal.Quotient.mk I)) Ideal.Quotient.mk_surjective
    apply isEffectiveCartierCenter_iff_isInvertible_ker.mpr
    apply Scheme.IdealSheafData.IsInvertible.of_isAffine
    rw [Scheme.Hom.ker_apply]
    change (RingHom.ker j.appTop.hom).IsRegularPrincipal
    have hk : RingHom.ker j.appTop.hom =
        I.comap (ΓSpecIso (CommRingCat.of A)).hom.hom := by
      ext s
      rw [RingHom.mem_ker, Ideal.mem_comap]
      have hh := congrArg (fun k ↦ k s)
        (ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk I)))
      change (ΓSpecIso (CommRingCat.of (A ⧸ I))).hom (j.appTop s) =
        Ideal.Quotient.mk I ((ΓSpecIso (CommRingCat.of A)).hom s) at hh
      rw [← Ideal.Quotient.eq_zero_iff_mem, ← hh]
      exact (map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
        (ΓSpecIso (CommRingCat.of (A ⧸ I))).hom).1).symm
    rw [hk]
    exact (Ideal.isRegularPrincipal_span_singleton_of_isRegular htr).comap_of_bijective
      (ConcreteCategory.bijective_of_isIso _)
  have hV : ∀ z : N, z ∈ V ↔ z ∉ Set.range j := by
    intro z
    change algebraMap H A g ∉ z.asIdeal ↔
      z ∉ Set.range (PrimeSpectrum.comap (Ideal.Quotient.mk I))
    rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
      Ideal.mk_ker, PrimeSpectrum.zeroLocus_span]
    change algebraMap H A g ∉ z.asIdeal ↔ ¬ ({t} : Set A) ⊆ z.asIdeal
    have htg : t ^ Nat.card G = algebraMap H A g := root_pow H g (Nat.card G)
    rw [Set.singleton_subset_iff, ← htg]
    exact not_congr (z.isPrime.pow_mem_iff_mem (Nat.card G) (Nat.card_pos (α := G)))
  have hN : IsLocallyNoetherian N := inferInstance
  let : IsIntegral D := hDI
  let η := genericPoint D
  have hη : IsGenericPoint η Set.univ := genericPoint_spec D
  obtain ⟨C, n, hn, hnV, O, hO, hnO, ζ, hζ⟩ :=
    W.strict_hensel_root_tame_normalization i G R φ f hG hf β hβ barY b hb
      hg hN D j hD hDI hj hV η hη
  exact ⟨hN, D, j, hD, hDI, hj, hV, C, n, hn, hnV, O, η, hη, hO, hnO, ζ, hζ⟩

end AlgebraicGeometry.Scheme
