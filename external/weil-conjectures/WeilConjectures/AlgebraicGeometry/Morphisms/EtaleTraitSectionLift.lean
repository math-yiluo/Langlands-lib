/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.RingTheory.DiscreteValuationRing.Basic

import WeilConjectures.AlgebraicGeometry.Morphisms.EtaleTraitStalk
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! Etale local trait lifts of sections.

## References

* Stacks Project, Tag 0EYI, preliminary paragraph
* Tag 0AP2 (15.45.4)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- A pointed etale neighbourhood of a trait section supplies an unramified trait lift. -/
theorem etale_trait_section_lift (R : CommRingCat.{u})
    [IsDomain R] [IsDiscreteValuationRing R]
    {L : Scheme.{u}} (p : L ⟶ Spec R) (τ : Spec R ⟶ L) (hτ : τ ≫ p = 𝟙 _)
    (B : CommRingCat.{u}) (φ : Spec B ⟶ L) (y : Spec B) (hφ : Etale φ)
    (hy : φ y = τ (IsLocalRing.closedPoint R))
    (ρ : R →+* B) (hρ : φ ≫ p = Spec.map (CommRingCat.ofHom ρ))
    (ϖ₀ : R) (hϖ₀ : IsLocalRing.maximalIdeal R = Ideal.span {ϖ₀}) :
    ∃ (A : CommRingCat.{u}) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
      (δ : R →+* A) (ι : B →+* A),
      Function.Injective δ ∧
      IsLocalRing.maximalIdeal A = Ideal.span {δ ϖ₀} ∧
      ι (ρ ϖ₀) = δ ϖ₀ ∧
      Spec.map (CommRingCat.ofHom ι) ≫ φ =
        Spec.map (CommRingCat.ofHom δ) ≫ τ := by
  have : Etale φ := hφ
  let X := pullback φ τ
  let f : X ⟶ Spec R := pullback.snd φ τ
  obtain ⟨x, _, hx⟩ :=
    Pullback.exists_preimage_pullback (f := φ) (g := τ) y (IsLocalRing.closedPoint R) hy
  obtain ⟨hA, hAd, hδ, hmax⟩ := etale_trait_stalk R f x hx ϖ₀ hϖ₀
  let A := X.presheaf.stalk x
  let : IsDomain A := hA
  let : IsDiscreteValuationRing A := hAd
  let δ : R →+* A := (StructureSheaf.toStalk R (f x) ≫ f.stalkMap x).hom
  let g : X ⟶ Spec B := pullback.fst φ τ
  let ι : B →+* A := (StructureSheaf.toStalk B (g x) ≫ g.stalkMap x).hom
  have hδspec : Spec.map (CommRingCat.ofHom δ) = X.fromSpecStalk x ≫ f := by
    rw [← SpecMap_stalkMap_fromSpecStalk f, Spec.fromSpecStalk_eq', ← Spec.map_comp]
    rfl
  have hιspec : Spec.map (CommRingCat.ofHom ι) = X.fromSpecStalk x ≫ g := by
    rw [← SpecMap_stalkMap_fromSpecStalk g, Spec.fromSpecStalk_eq', ← Spec.map_comp]
    rfl
  have hsquare : Spec.map (CommRingCat.ofHom ι) ≫ φ =
      Spec.map (CommRingCat.ofHom δ) ≫ τ := by
    rw [hδspec, hιspec, Category.assoc, Category.assoc]
    exact congrArg (X.fromSpecStalk x ≫ ·) (pullback.condition (f := φ) (g := τ))
  have hring : CommRingCat.ofHom ρ ≫ CommRingCat.ofHom ι = CommRingCat.ofHom δ := by
    apply Spec.map_injective
    rw [Spec.map_comp, ← hρ, ← Category.assoc, hsquare, Category.assoc, hτ]
    exact Category.comp_id (Spec.map (CommRingCat.ofHom δ))
  refine ⟨A, hA, hAd, δ, ι, hδ, hmax, ?_, hsquare⟩
  exact congrArg (fun h : R ⟶ A ↦ h.hom ϖ₀) hring


end AlgebraicGeometry.Scheme
