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

import WeilConjectures.AlgebraicGeometry.Morphisms.RootDivisorGenericPrime
import WeilConjectures.AlgebraicGeometry.Morphisms.RootNormalizationCotangentRoot
import Mathlib.RingTheory.Nakayama

/-! # RootNormalizationGenericStalkMaximalIdeal

## References

* Stacks Project, Tags 09EB, 0BRM and 0EYG
* Stacks Project, 0BRM, 0307, and 09E7
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The root extension makes the base maximal ideal generate each normalization
stalk maximal ideal above the divisor generic point. -/
theorem root_normalization_generic_stalk_maximalIdeal
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
        (IsLocalRing.maximalIdeal (N.presheaf.stalk (a.fromNormalization x))).map
          (a.fromNormalization.stalkMap x).hom =
            IsLocalRing.maximalIdeal (a.normalization.presheaf.stalk x) := by
  dsimp only
  intro hroot hN hp hetale hfinite D j hDreg hD hj hV η hη x hx
  let := hN
  let := hp
  let g := b.hom f
  let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
  let N := Spec (CommRingCat.of A)
  let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
  let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
  let a := p ≫ V.ι
  let t : A := AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G -
    Polynomial.C g)
  let y := a.fromNormalization x
  have hy : y.asIdeal = Ideal.span {t} := by
    rw [show y = j η from hx]
    exact root_divisor_generic_prime H g (Nat.card G) Nat.card_pos D j hj hV η hη
  have hreg : IsRegularLocalRing (N.presheaf.stalk y) := by
    have ht : t ∈ y.asIdeal := hy ▸ Ideal.subset_span (Set.mem_singleton _)
    let := hroot y.asIdeal y.isPrime ht
    exact IsRegularLocalRing.of_ringEquiv
      (AlgebraicGeometry.StructureSheaf.stalkIso A y).toRingEquiv
  let : Algebra A (N.presheaf.stalk y) :=
    (AlgebraicGeometry.StructureSheaf.toStalk A y).hom.toAlgebra
  have : IsLocalization.AtPrime (N.presheaf.stalk y) y.asIdeal :=
    inferInstanceAs (IsLocalization.AtPrime
      ((AlgebraicGeometry.Spec.structureSheaf A).presheaf.stalk y) y.asIdeal)
  have hbase : IsLocalRing.maximalIdeal (N.presheaf.stalk y) =
      Ideal.span {AlgebraicGeometry.StructureSheaf.toStalk A y t} := by
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (R := A) y.asIdeal (N.presheaf.stalk y), hy]
    simp only [Ideal.map_span, Set.image_singleton]
    rfl
  let := hfinite
  have : IsLocallyNoetherian a.normalization :=
    LocallyOfFiniteType.isLocallyNoetherian a.fromNormalization
  let C := a.normalization.presheaf.stalk x
  let m := IsLocalRing.maximalIdeal C
  let v := (a.fromNormalization.stalkMap x).hom
  let J := (IsLocalRing.maximalIdeal (N.presheaf.stalk y)).map v
  have hcot := root_normalization_cotangent_root i G W R φ f β hβ H b hG hg
    hN hp hetale hfinite x hy hreg
  have hle : m ≤ J ⊔ m • m := by
    dsimp only [J]
    rw [hbase, Ideal.map_span, Set.image_singleton, Ideal.smul_eq_mul]
    exact hcot
  apply le_antisymm
  · exact IsLocalRing.map_maximalIdeal_le v
  · exact Submodule.le_of_le_smul_of_le_jacobson_bot
      (IsNoetherian.noetherian m) (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal C)) hle

end AlgebraicGeometry.Scheme
