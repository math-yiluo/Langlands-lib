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

import WeilConjectures.AlgebraicGeometry.FundamentalGroup.ExtendOverInertia
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationFinite
import WeilConjectures.AlgebraicGeometry.Morphisms.StrictHenselRootNormalizationGenericEtale

/-! # Tame normalization after the group-order root extension

## References

* Stacks Project, Tags 09EB, 0BRM, 0EYG and 0EYH
* Stacks Project, Tag 0EYG, root-extension paragraph, Tag 09EB and Tag 0BRM
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem finite_etale_over_basicOpen
    {L U T P : Scheme.{u}} (i : U ⟶ L) (w : P ⟶ U)
    [IsFinite w] [Etale w] (R : CommRingCat.{u}) (φ : Spec R ⟶ L) (f : R)
    (β : pullback i φ ≅ Scheme.Opens.toScheme (X := Spec R) (PrimeSpectrum.basicOpen f))
    (hβ : β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) =
      pullback.snd i φ)
    (ψ : T ⟶ Spec R)
    (hψ : ∀ t : T, ψ t ∈ (PrimeSpectrum.basicOpen f : (Spec R).Opens)) :
    IsFinite (pullback.snd (w ≫ i) (ψ ≫ φ)) ∧
      Etale (pullback.snd (w ≫ i) (ψ ≫ φ)) := by
  let F : (Spec R).Opens := PrimeSpectrum.basicOpen f
  let δ : T ⟶ F.toScheme := IsOpenImmersion.lift F.ι ψ (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact hψ t)
  have hδ : δ ≫ F.ι = ψ := IsOpenImmersion.lift_fac F.ι ψ _
  let k : T ⟶ pullback i φ := δ ≫ β.inv
  have hk : k ≫ pullback.snd i φ = ψ := by
    rw [← hβ]
    simp only [k, Category.assoc, Iso.inv_hom_id_assoc]
    exact hδ
  let a := pullback.lift (f := i) (g := ψ ≫ φ)
    (k ≫ pullback.fst i φ) (𝟙 T) (by
      rw [Category.id_comp, Category.assoc, pullback.condition, ← Category.assoc, hk])
  let r := pullback.lift (f := i) (g := φ) (pullback.fst i (ψ ≫ φ))
    (pullback.snd i (ψ ≫ φ) ≫ ψ) (by
      simpa only [Category.assoc] using pullback.condition (f := i) (g := ψ ≫ φ))
  have hr : r ≫ β.hom = pullback.snd i (ψ ≫ φ) ≫ δ := by
    apply (cancel_mono F.ι).mp
    change r ≫ β.hom ≫ Scheme.Opens.ι (X := Spec R) (PrimeSpectrum.basicOpen f) = _
    rw [hβ]
    dsimp only [r]
    rw [pullback.lift_snd]
    rw [Category.assoc, hδ]
  have hrk : r = pullback.snd i (ψ ≫ φ) ≫ k := by
    rw [← cancel_mono β.hom]
    simpa only [k, Category.assoc, Iso.inv_hom_id, Category.comp_id] using hr
  let e : pullback i (ψ ≫ φ) ≅ T :=
    { hom := pullback.snd i (ψ ≫ φ)
      inv := a
      hom_inv_id := by
        apply pullback.hom_ext
        · simp only [Category.assoc, a, pullback.lift_fst, Category.id_comp]
          simpa only [r, pullback.lift_fst, Category.assoc] using
            congrArg (fun t ↦ t ≫ pullback.fst i φ) hrk.symm
        · simp only [Category.assoc, a, pullback.lift_snd, Category.comp_id,
            Category.id_comp]
      inv_hom_id := by simp only [a, pullback.lift_snd] }
  let E := pullbackRightPullbackFstIso i (ψ ≫ φ) w
  have heq : pullback.snd (w ≫ i) (ψ ≫ φ) =
      E.inv ≫ pullback.snd w (pullback.fst i (ψ ≫ φ)) ≫ e.hom := by
    simpa only [e] using
      (pullbackRightPullbackFstIso_inv_snd_snd i (ψ ≫ φ) w).symm
  have : IsIso (pullback.snd i (ψ ≫ φ)) := e.isIso_hom
  rw [heq]
  exact ⟨inferInstance, inferInstance⟩

private noncomputable def normalization_restrict_iso
    {X N : Scheme.{u}} (V : N.Opens) (p : X ⟶ V.toScheme)
    [IsFinite p] [QuasiCompact V.ι] :
    ((p ≫ V.ι).fromNormalization ⁻¹ᵁ V).toScheme ≅ X :=
  (pullbackRestrictIsoRestrict (p ≫ V.ι).fromNormalization V).symm ≪≫
    Scheme.Hom.pullbackFromNormalizationIso p V.ι

private theorem normalization_restrict_iso_hom_comp
    {X N : Scheme.{u}} (V : N.Opens) (p : X ⟶ V.toScheme)
    [IsFinite p] [QuasiCompact V.ι] :
    (normalization_restrict_iso V p).hom ≫ p = (p ≫ V.ι).fromNormalization ∣_ V := by
  simp only [normalization_restrict_iso, Iso.trans_hom, Category.assoc,
    Scheme.Hom.pullbackFromNormalizationIso_hom_comp]
  rfl

/-- The pulled-back cover has a finite normalization etale near the divisor generic point. -/
theorem GaloisCover.strict_hensel_root_tame_normalization
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
    ¬ IsUnit g → IsLocallyNoetherian N →
    ∀ (D : Scheme.{u}) (j : D ⟶ N),
      IsRegular D → IsIntegral D → IsEffectiveCartierCenter j →
      (∀ z : N, z ∈ V ↔ z ∉ Set.range j) →
      ∀ (η : D), IsGenericPoint η Set.univ →
      ∃ (C : Scheme.{u}) (n : C ⟶ N),
        IsFinite n ∧ Etale (n ∣_ V) ∧
        ∃ (O : N.Opens), j η ∈ O ∧ Etale (n ∣_ O) ∧
        ∃ ζ : (n ⁻¹ᵁ V).toScheme ≅
            pullback (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ),
          ζ.hom ≫ pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ) =
            n ∣_ V := by
  dsimp only
  intro hgu hN D j hD hDi hj hV η hη
  let H := strictHenselization barY
  let g := b.hom f
  let A := AdjoinRoot ((Polynomial.X : Polynomial H) ^ Nat.card G - Polynomial.C g)
  let N := Spec (CommRingCat.of A)
  let q := Spec.map (CommRingCat.ofHom (algebraMap H A))
  let V : N.Opens := PrimeSpectrum.basicOpen (algebraMap H A g)
  let ψ := V.ι ≫ q ≫ Spec.map b
  let p := pullback.snd (W.π ≫ i) (V.ι ≫ q ≫ Spec.map b ≫ φ)
  have : IsFinite W.π := W.isFinite
  have : Etale W.π := W.etale
  have hpψ : ∀ v : V.toScheme,
      ψ v ∈ (PrimeSpectrum.basicOpen f : (Spec R).Opens) := by
    intro v
    change algebraMap H A g ∉ (V.ι v).asIdeal
    exact v.property
  have hp : IsFinite p ∧ Etale p := by
    have h := finite_etale_over_basicOpen i W.π R φ f β hβ ψ hpψ
    have hψφ : ψ ≫ φ = V.ι ≫ q ≫ Spec.map b ≫ φ := by
      dsimp only [ψ]
      rw [Category.assoc, Category.assoc]
    rw [hψφ] at h
    exact h
  have : IsFinite p := hp.1
  have : Etale p := hp.2
  have : IsLocallyNoetherian N := hN
  let a := p ≫ V.ι
  have hn : IsFinite a.fromNormalization :=
    W.strict_hensel_root_normalization_finite i G R φ f hf barY b hb
      hgu hN hp.1 hp.2
  obtain ⟨O, hO, heO⟩ :=
    W.strict_hensel_root_normalization_generic_etale i G R φ f hG hf β hβ barY b hb
      hgu hN hp.1 hp.2 hn D j hD hDi hj hV η hη
  let ζ := normalization_restrict_iso V p
  have hζ : ζ.hom ≫ p = a.fromNormalization ∣_ V :=
    normalization_restrict_iso_hom_comp V p
  have heV : Etale (a.fromNormalization ∣_ V) := by
    rw [← hζ]
    infer_instance
  exact ⟨a.normalization, a.fromNormalization, hn, heV, O, hO, heO, ζ, hζ⟩

end AlgebraicGeometry.Scheme
