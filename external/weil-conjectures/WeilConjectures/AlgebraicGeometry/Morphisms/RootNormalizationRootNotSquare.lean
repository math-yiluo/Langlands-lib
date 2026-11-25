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
public import Mathlib.AlgebraicGeometry.Normalization
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.Morphisms.DvrRootNormalizationMaximalIdeal
import WeilConjectures.AlgebraicGeometry.Morphisms.RootNormalizationDvrComparison
import WeilConjectures.AlgebraicGeometry.Morphisms.NormalizationStalkRegularBasicOpen
import Mathlib.RingTheory.LocalRing.RingHom.Basic

/-! # The tame root has nonzero first-order class

## References

* Stacks Project, Tags 09EB, 0BRM, 09E7 and 0307
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem regular_generator_not_mem_square
    {C : Type u} [CommRing C] (m : Ideal C) (tau : C)
    (hm : m = Ideal.span {tau}) (hproper : m ≠ ⊤) (hreg : IsRegular tau) :
    tau ∉ m * m := by
  intro h
  have h' : tau ∈ Ideal.span {tau} * m := by rwa [← hm]
  obtain ⟨z, hz, he⟩ := Ideal.mem_span_singleton_mul.mp h'
  have hz1 : z = 1 := hreg.left (he.trans (mul_one tau).symm)
  apply hproper
  exact m.eq_top_of_isUnit_mem (hz1 ▸ hz) isUnit_one

private theorem maximalIdeal_eq_span_of_equiv
    {C D : Type u} [CommRing C] [CommRing D] [IsLocalRing C] [IsLocalRing D]
    (e : D ≃+* C) (s : D) (t : C)
    (hs : IsLocalRing.maximalIdeal D = Ideal.span {s}) (he : e s = t) :
    IsLocalRing.maximalIdeal C = Ideal.span {t} := by
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e, hs, Ideal.map_span,
    Set.image_singleton, he]

/-- The image of the root does not belong to the square of the normalized maximal ideal. -/
theorem root_normalization_root_not_square
    {L U : Scheme.{u}} (i : U ⟶ L)
    (G : Type (u + 1)) [Group G] [Finite G] (W : GaloisCover G U)
    (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R)
      (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R)
      (PrimeSpectrum.basicOpen f) = pullback.snd i φ)
    (H : CommRingCat.{u}) [IsNoetherianRing H] (b : R ⟶ H)
    (hG : IsUnit (Nat.card G : H)) (hg : IsSMulRegular H (b.hom f))
    [IsDomain (H ⧸ Ideal.span {b.hom f})] :
    let g := b.hom f
    let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
    let N := Spec (CommRingCat.of A)
    let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
    let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
    ∀ (hN : IsLocallyNoetherian N),
    let := hN
    let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
    ∀ (hp : IsFinite p),
    let := hp
    let a := p ≫ V.ι
    Etale p → IsFinite a.fromNormalization →
    ∀ (x : a.normalization),
      (a.fromNormalization x).asIdeal = Ideal.span
        {AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)} →
      IsRegularLocalRing (N.presheaf.stalk (a.fromNormalization x)) →
      let C := a.normalization.presheaf.stalk x
      let m := IsLocalRing.maximalIdeal C
      let t := AlgebraicGeometry.StructureSheaf.toStalk A (a.fromNormalization x)
        (AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g))
      (a.fromNormalization.stalkMap x).hom t ∉ m * m := by
  dsimp only
  intro hN hp hEtale hNorm x hx _hroot
  let := hN
  let := hp
  let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C (b.hom f))
  let N := Spec (CommRingCat.of A)
  let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A (b.hom f))
  let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
  let a := p ≫ V.ι
  let C := a.normalization.presheaf.stalk x
  let t : A := AdjoinRoot.root
    ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C (b.hom f))
  let rho : A →+* C := (a.fromNormalization.stalkMap x).hom.comp
    (AlgebraicGeometry.StructureSheaf.toStalk A (a.fromNormalization x)).hom
  have ht : t ^ Nat.card G = algebraMap H A (b.hom f) := by
    change AdjoinRoot.root _ ^ Nat.card G =
      algebraMap H (AdjoinRoot _) (b.hom f)
    rw [AdjoinRoot.algebraMap_eq]
    have he := AdjoinRoot.eval₂_root
      ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C (b.hom f))
    simpa only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C, sub_eq_zero, AdjoinRoot.algebraMap_eq] using he
  have hregg : IsRegular (rho (algebraMap H A (b.hom f))) :=
    normalization_stalk_regular_basicOpen (CommRingCat.of A)
      (algebraMap H A (b.hom f)) p x
  have hreg : IsRegular (rho t) := by
    apply (IsRegular.pow_iff (Nat.card_pos (α := G))).mp
    rwa [← map_pow, ht]
  have hmodel := root_normalization_dvr_comparison i G W R φ f β hβ H b hG hg
    hN hp hEtale hNorm x hx
  obtain ⟨B, hB, hmodel⟩ := hmodel
  let := hB
  obtain ⟨hDvr, hmodel⟩ := hmodel
  let := hDvr
  obtain ⟨pi, hpi, hn, T, hmodel⟩ := hmodel
  obtain ⟨hqc, hqs, hmodel⟩ := hmodel
  let := hqc
  let := hqs
  obtain ⟨hNorm0, x0, hx0, e, he⟩ := hmodel
  have hm0 := dvr_root_normalization_maximalIdeal B pi hpi G T hn
    hqc hqs hNorm0 x0 hx0
  have hm : IsLocalRing.maximalIdeal C = Ideal.span {rho t} :=
    maximalIdeal_eq_span_of_equiv e _ _ hm0 he
  exact regular_generator_not_mem_square (IsLocalRing.maximalIdeal C) (rho t)
    hm (IsLocalRing.maximalIdeal.isMaximal C).ne_top hreg

end AlgebraicGeometry.Scheme
