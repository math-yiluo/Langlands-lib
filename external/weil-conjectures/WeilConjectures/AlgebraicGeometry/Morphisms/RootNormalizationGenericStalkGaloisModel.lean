/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTorsor
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.Algebra.Regular.SMul
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Regular
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Localization.Ideal

public import Mathlib.NumberTheory.RamificationInertia.Galois

import WeilConjectures.AlgebraicGeometry.Morphisms.CartierGenericStalkGaloisModel
import WeilConjectures.AlgebraicGeometry.Morphisms.RegularCartierGenericStalkDvr

/-! # A Galois integral-closure model at the root divisor generic point

## References

* Stacks Project, Tags 0307 and 09EB
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem basicOpen_pullback_torsor_square
    {L U N : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R)
      (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R)
      (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    (v : N ⟶ Spec R) (V : N.Opens)
    (hv : V = v ⁻¹ᵁ PrimeSpectrum.basicOpen f) :
    ∃ κ : V.toScheme ⟶ U,
      IsPullback (pullback.fst (W.π ≫ i) (V.ι ≫ v ≫ φ))
        (pullback.snd (W.π ≫ i) (V.ι ≫ v ≫ φ)) W.π κ := by
  subst V
  let O : (Spec R).Opens := PrimeSpectrum.basicOpen f
  have hβpb : IsPullback (β.inv ≫ pullback.fst i φ) O.ι i φ := by
    apply (IsPullback.of_hasPullback i φ).of_iso β (Iso.refl _) (Iso.refl _) (Iso.refl _)
    · simp
    · simpa only [Iso.refl_hom, Category.comp_id] using hβ.symm
    · simp
    · simp
  let κ := (v ∣_ O) ≫ β.inv ≫ pullback.fst i φ
  have hκ : IsPullback κ (v ⁻¹ᵁ O).ι i (v ≫ φ) := by
    simpa only [Category.assoc, κ] using
      ((isPullback_morphismRestrict v O).flip.paste_vert hβpb.flip).flip
  have hself : IsPullback (𝟙 (v ⁻¹ᵁ O).toScheme) (𝟙 (v ⁻¹ᵁ O).toScheme)
      (v ⁻¹ᵁ O).ι (v ⁻¹ᵁ O).ι :=
    IsPullback.of_vert_isIso_mono ⟨by simp⟩
  have hκ' : IsPullback κ (𝟙 (v ⁻¹ᵁ O).toScheme) i ((v ⁻¹ᵁ O).ι ≫ v ≫ φ) := by
    simpa only [Category.id_comp, Category.assoc] using hself.paste_horiz hκ
  have h := (IsPullback.of_hasPullback (W.π ≫ i) ((v ⁻¹ᵁ O).ι ≫ v ≫ φ)).of_bot' hκ'
  refine ⟨κ, ?_⟩
  have he := hκ'.lift_snd
    (pullback.fst (W.π ≫ i) ((v ⁻¹ᵁ O).ι ≫ v ≫ φ) ≫ W.π)
    (pullback.snd (W.π ≫ i) ((v ⁻¹ᵁ O).ι ≫ v ≫ φ))
    (by rw [Category.assoc, pullback.condition])
  simp only [Category.comp_id] at he
  simpa only [he] using h

set_option linter.unusedVariables false in
/-- A root-normalization residue extension has a finite flat Galois integral-closure model. -/
theorem root_normalization_generic_stalk_galois_model
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R)
      (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R)
      (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    (H : CommRingCat.{u}) [IsNoetherianRing H] (b : R ⟶ H)
    (hg : IsSMulRegular H (b.hom f))
    [IsDomain (H ⧸ Ideal.span {b.hom f})] :
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    (∀ (Q : Ideal A) (hQ : Q.IsPrime),
      letI := hQ
      AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g) ∈ Q →
        IsRegularLocalRing (Localization.AtPrime Q)) →
    ∀ (hN : IsLocallyNoetherian N),
    letI := hN
    let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
    ∀ (hp : IsFinite p),
    letI := hp
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization →
    ∀ (D : Scheme.{u}) (j : D ⟶ N),
      IsRegular D → IsIntegral D → IsEffectiveCartierCenter j →
      (∀ z : N, z ∈ V ↔ z ∉ Set.range j) →
      ∀ (η : D), IsGenericPoint η Set.univ →
      ∀ (x : a.normalization), a.fromNormalization x = j η →
        ∃ (S : CommRingCat.{u}) (T : Subgroup G)
          (alg : Algebra (N.presheaf.stalk (j η)) S),
          letI := alg
          ∃ (act : MulSemiringAction T S),
          letI := act
          IsDomain (N.presheaf.stalk (j η)) ∧ IsDomain S ∧
          Module.Finite (N.presheaf.stalk (j η)) S ∧
          Module.Flat (N.presheaf.stalk (j η)) S ∧
          IsGaloisGroup T (N.presheaf.stalk (j η)) S ∧
          ∃ (q₀ : Ideal S), q₀.IsPrime ∧
            (letI := (a.fromNormalization.residueFieldMap x).hom.toAlgebra
             Module.finrank (N.residueField (a.fromNormalization x))
               (a.normalization.residueField x)) = q₀.inertiaDeg (N.presheaf.stalk (j η)) := by
  dsimp only
  intro hroot hN hp hetale hfinite D j hDreg hD hj hV η hη x hx
  let := hN
  let := hp
  let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C (b.hom f))
  let N := Spec (CommRingCat.of A)
  let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A (b.hom f))
  have hs : j η ∉ V := by
    intro hs
    exact (hV (j η)).mp hs ⟨η, rfl⟩
  have ht : AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G -
      Polynomial.C (b.hom f)) ∈ (j η).asIdeal := by
    have hg' : algebraMap H A (b.hom f) ∈ (j η).asIdeal := by
      exact Classical.not_not.mp hs
    have heq : AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G -
        Polynomial.C (b.hom f)) ^ Nat.card G = algebraMap H A (b.hom f) := by
      have heval := AdjoinRoot.eval₂_root
        ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C (b.hom f))
      simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
        Polynomial.eval₂_C, sub_eq_zero, ← AdjoinRoot.algebraMap_eq] using heval
    exact ((j η).isPrime.pow_mem_iff_mem (Nat.card G) Nat.card_pos).mp (heq ▸ hg')
  have hreg : IsRegularLocalRing (N.presheaf.stalk (j η)) := by
    let := hroot (j η).asIdeal (j η).isPrime ht
    exact IsRegularLocalRing.of_ringEquiv
      (AlgebraicGeometry.StructureSheaf.stalkIso A (j η)).toRingEquiv
  have hdata : ∃ hdom : IsDomain (N.presheaf.stalk (j η)),
      letI := hdom
      IsDiscreteValuationRing (N.presheaf.stalk (j η)) := by
    exact regular_cartier_generic_stalk_dvr (X := N) j hD hj η hη hreg
  obtain ⟨hdom, hdvr⟩ := hdata
  have hv : V = (q ≫ Spec.map b) ⁻¹ᵁ PrimeSpectrum.basicOpen f := by
    dsimp only [q, V]
    rw [Scheme.Hom.comp_preimage, SpecMap_preimage_basicOpen, SpecMap_preimage_basicOpen]
    rfl
  have hpbs : ∃ κ : V.toScheme ⟶ U,
      IsPullback (pullback.fst (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ))
        (pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)) W.π κ := by
    have h := basicOpen_pullback_torsor_square (N := N) i G W R φ f β hβ
      (q ≫ Spec.map b) V hv
    rw [Category.assoc] at h
    exact h
  obtain ⟨κ, hpb⟩ := hpbs
  have hmodel := cartier_generic_stalk_galois_model (N := N) G W V κ
    (pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ))
    (pullback.fst (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)) hpb
  dsimp only at hmodel
  exact hmodel hetale hfinite D j hD hj hV η hη hdom hdvr x hx

end AlgebraicGeometry.Scheme
