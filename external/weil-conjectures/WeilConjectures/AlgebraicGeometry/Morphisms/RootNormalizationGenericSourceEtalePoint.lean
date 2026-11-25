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

import WeilConjectures.AlgebraicGeometry.Morphisms.RootNormalizationGenericStalkFlat
import WeilConjectures.AlgebraicGeometry.Morphisms.RootNormalizationGenericStalkUnramified
import WeilConjectures.AlgebraicGeometry.Morphisms.FiniteFlatTargetLocus
import WeilConjectures.AlgebraicGeometry.Morphisms.FormallyUnramifiedStalkNeighbourhood

/-! # Abhyankar's lemma at a point of the generic root-divisor fibre

## References

* Stacks Project, Tags 09EB, 0BRM and 0EYG
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

private theorem etale_neighbourhood_of_fibre_flat_stalks
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f] [IsLocallyNoetherian Y]
    (y : Y) (hflat : ∀ z : X, f z = y → (f.stalkMap z).hom.Flat)
    (x : X) (hxy : f x = y) (hu : (f.stalkMap x).hom.FormallyUnramified) :
    ∃ E : X.Opens, x ∈ E ∧ Etale (E.ι ≫ f) := by
  let F : Y.Opens := ⟨{w | ∀ z : X, f z = w → (f.stalkMap z).hom.Flat},
    isOpen_setOf_finite_flat_stalks f⟩
  have hyF : y ∈ F := hflat
  have hF : Flat (f ∣_ F) := by
    apply Flat.of_stalkMap
    intro z
    exact (RingHom.Flat.respectsIso.arrow_mk_iso_iff
      (morphismRestrictStalkMap f F z)).mpr (z.2 z.1 rfl)
  obtain ⟨B, hxB, hB⟩ := FormallyUnramified.exists_neighbourhood_of_stalkMap f x hu
  let E := B ⊓ f ⁻¹ᵁ F
  have heB : E ≤ B := inf_le_left
  have heF : E ≤ f ⁻¹ᵁ F := inf_le_right
  have hflatE : Flat (E.ι ≫ f) := by
    have : Flat (f ∣_ F) := hF
    have : Flat ((X.homOfLE heF) ≫ (f ∣_ F) ≫ F.ι) := inferInstance
    simpa only [Category.assoc, morphismRestrict_ι, Scheme.homOfLE_ι_assoc] using this
  have hunramE : FormallyUnramified (E.ι ≫ f) := by
    have : FormallyUnramified (B.ι ≫ f) := hB
    have : FormallyUnramified ((X.homOfLE heB) ≫ (B.ι ≫ f)) :=
      MorphismProperty.comp_mem @FormallyUnramified _ _ inferInstance hB
    simpa only [Scheme.homOfLE_ι_assoc] using this
  have : Flat (E.ι ≫ f) := hflatE
  have : FormallyUnramified (E.ι ≫ f) := hunramE
  exact ⟨E, ⟨hxB, by change f x ∈ F; rwa [hxy]⟩, Etale.of_formallyUnramified_of_flat (E.ι ≫ f)⟩

/-- **Abhyankar's lemma at a point.** For the normalization of the root cover in the given
chart, every point lying over the generic point `η` of the regular divisor `D` has an open
neighbourhood that is étale over `N`. -/
theorem root_normalization_generic_source_etale_point
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
        ∃ E : a.normalization.Opens, x ∈ E ∧
          Etale (E.ι ≫ a.fromNormalization) := by
  dsimp only
  intro hroot hN hp he hn D j hD hDi hj hV η hη x hx
  have := hN
  have := hp
  have := hn
  have hflat := root_normalization_generic_stalk_flat H (b.hom f) hg (Nat.card G)
    Nat.card_pos hroot hN _ _ hp he hn D j hDi hj hV η hη
  have hu := root_normalization_generic_stalk_unramified i G W R φ f β hβ H b hG hg
    hroot hN hp he hn D j hD hDi hj hV η hη x hx
  exact etale_neighbourhood_of_fibre_flat_stalks _ (j η) hflat x hx hu

end AlgebraicGeometry.Scheme
