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
import WeilConjectures.AlgebraicGeometry.Morphisms.RootNormalizationStalkPrincipalIdeal
import WeilConjectures.AlgebraicGeometry.Morphisms.RootNormalizationRootNotSquare

/-! # The cotangent root class after tame normalization

## References

* Stacks Project, Tag 09EB (Galois degree formula), Tag 0BRM (Abhyankar), Tag 09E7 (index-one
  clause), and Tag 0307 (localization of integral closure)
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- The root class spans the cotangent space of each normalized factor at the root prime. -/
theorem root_normalization_cotangent_root
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
    letI := hN
    let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
    ∀ (hp : IsFinite p),
    letI := hp
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
      m ≤ Ideal.span {(a.fromNormalization.stalkMap x).hom t} ⊔ m * m := by
  dsimp
  intro hN
  let := hN
  intro hp
  let := hp
  intro h_etale h_fin x hx hreg
  let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C (b.hom f))
  let N := Spec (CommRingCat.of A)
  let : IsLocallyNoetherian N := hN
  let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A (b.hom f))
  let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
  let : IsFinite p := hp
  let a := p ≫ V.ι
  let C := a.normalization.presheaf.stalk x
  let m := IsLocalRing.maximalIdeal C
  let τ : C := (a.fromNormalization.stalkMap x).hom
    (AlgebraicGeometry.StructureSheaf.toStalk A (a.fromNormalization x)
      (AdjoinRoot.root ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C (b.hom f))))
  have hm : m.IsPrincipal := root_normalization_stalk_maximalIdeal_isPrincipal H (b.hom f)
    hg (Nat.card G) (Nat.card_pos) hN _ p hp h_etale h_fin x hx hreg
  have hτ : τ ∉ m * m := root_normalization_root_not_square i G W R φ f β hβ H b hG hg
    hN hp h_etale h_fin x hx hreg
  change m ≤ Ideal.span {τ} ⊔ m * m
  apply le_trans (b := Ideal.span {τ}) _ le_sup_left
  by_cases hunit : IsUnit τ
  · rw [Ideal.span_singleton_eq_top.mpr hunit]
    exact le_top
  obtain ⟨r, hr⟩ := Submodule.IsPrincipal.principal m
  have hrmem : r ∈ m := hr.symm ▸ Ideal.mem_span_singleton_self r
  have hτmem : τ ∈ m := hunit
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp (hr ▸ hτmem)
  have hcunit : IsUnit c := by
    by_contra hcunit
    have hcmem : c ∈ m := hcunit
    exact hτ (hc ▸ Ideal.mul_mem_mul hcmem hrmem)
  intro z hz
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp (hr ▸ hz)
  obtain ⟨v, hv⟩ := hcunit
  apply Ideal.mem_span_singleton'.mpr
  refine ⟨d * (↑v⁻¹ : C), ?_⟩
  rw [← hc, ← hv]
  simpa [mul_assoc] using hd

end AlgebraicGeometry.Scheme
