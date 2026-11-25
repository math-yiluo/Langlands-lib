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

import Mathlib.RingTheory.Unramified.LocalRing
import WeilConjectures.AlgebraicGeometry.Morphisms.RootNormalizationGenericStalkMaximalIdeal
import WeilConjectures.AlgebraicGeometry.Morphisms.RootNormalizationGenericResidueSeparable

/-! # Tame unramifiedness after the group-order root extension

## References

* Stacks Project, Tags 09EB, 0BRM and 0EYG, the root-extension calculation
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem formallyUnramified_stalkMap_of_maximalIdeal_and_residue
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] (x : X)
    (hm : (IsLocalRing.maximalIdeal (Y.presheaf.stalk (f x))).map
      (f.stalkMap x).hom = IsLocalRing.maximalIdeal (X.presheaf.stalk x))
    (hs : letI := (f.residueFieldMap x).hom.toAlgebra
      Algebra.IsSeparable (Y.residueField (f x)) (X.residueField x)) :
    (f.stalkMap x).hom.FormallyUnramified := by
  algebraize [(f.stalkMap x).hom]
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) :=
    inferInstanceAs <| IsLocalHom (f.stalkMap x).hom
  have : Algebra.EssFiniteType (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    LocallyOfFiniteType.stalkMap f x
  have hs' : Algebra.IsSeparable
      (IsLocalRing.ResidueField (Y.presheaf.stalk (f x)))
      (IsLocalRing.ResidueField (X.presheaf.stalk x)) := by
    convert! hs
    refine Algebra.algebra_ext _ _ fun r ↦ ?_
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective r
    rfl
  have := hs'
  exact Algebra.FormallyUnramified.of_map_maximalIdeal hm

/-- The group-order root extension kills ramification on normalization stalks. -/
theorem root_normalization_generic_stalk_unramified
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
        (a.fromNormalization.stalkMap x).hom.FormallyUnramified := by
  dsimp only
  intro hroot hN hp he hn D j hD hDi hj hV η hη x hx
  have := hN
  have := hp
  have := hn
  have hm := root_normalization_generic_stalk_maximalIdeal i G W R φ f β hβ H b hG hg
    hroot hN hp he hn D j hD hDi hj hV η hη x hx
  have hs := root_normalization_generic_stalk_residue_separable i G W R φ f β hβ H b hG hg
    hroot hN hp he hn D j hD hDi hj hV η hη x hx
  exact formallyUnramified_stalkMap_of_maximalIdeal_and_residue _ x hm hs


end AlgebraicGeometry.Scheme
