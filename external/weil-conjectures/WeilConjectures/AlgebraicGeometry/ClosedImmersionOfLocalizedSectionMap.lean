/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.Module.LocalizedModule.IsLocalization

/-!
# A surjective localized section map gives a closed immersion

Source: Stacks Project, Tag 04DG, proof, final localization sentence.
(blueprint: lem-weil-pbc-closed-immersion-localized-section-map).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem surjective_awayMap_of_localizedMap_surjective
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    [Algebra A B] [Algebra A A'] [Algebra B B'] (a : A)
    [IsLocalization.Away a A'] [IsLocalization.Away (algebraMap A B a) B']
    (h : Function.Surjective (LocalizedModule.map (Submonoid.powers a)
      (Algebra.linearMap A B))) :
    Function.Surjective (IsLocalization.Away.map A' B' (algebraMap A B) a) := by
  let : Algebra A B' := ((algebraMap B B').comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let g₁ := Algebra.linearMap A A'
  let g₂ := (Algebra.linearMap B B').restrictScalars A
  have : IsLocalizedModule (Submonoid.powers a) g₂ :=
    IsLocalizedModule.restrictScalars_powers a (Algebra.linearMap B B')
  let j : A →ₐ[A] B := ⟨algebraMap A B, fun _ ↦ rfl⟩
  have hj : IsLocalization.Away (j a) B' := inferInstanceAs
    (IsLocalization.Away (algebraMap A B a) B')
  let g := IsLocalization.Away.mapₐ j a (Aₚ := A') (Bₚ := B')
  have he : g.toLinearMap =
      IsLocalizedModule.map (Submonoid.powers a) g₁ g₂ (Algebra.linearMap A B) := by
    apply IsLocalizedModule.linearMap_ext (Submonoid.powers a) g₁ g₂
    apply LinearMap.ext
    intro x
    change g (g₁ x) = _
    rw [LinearMap.comp_apply, IsLocalizedModule.map_apply]
    exact g.commutes x
  have hg := (IsLocalizedModule.map_surjective_iff_localizedModuleMap_surjective
    g₁ g₂ (l := Algebra.linearMap A B)).mpr h
  rw [← he] at hg
  exact hg

set_option backward.isDefEq.respectTransparency false in
/-- Surjectivity of the localized affine section map makes the restriction over the
corresponding principal open a closed immersion.
Source: Stacks Project, Tag 04DG, proof, final localization sentence.
(blueprint: lem-weil-pbc-closed-immersion-localized-section-map).

Proof: Let A = Γ(S,U), B = Γ(X,f⁻¹U). The affine-morphism hypothesis makes f⁻¹U affine.
For a in A, the open S.basicOpen a is affine, and its inverse image is the affine
basic open defined by the image of a in B. Their section rings are A_a and B_a.
Localization commutes with the linear map A → B. The localized modules of A and B
are therefore their localized rings as A-modules, and the given surjectivity says
A_a → B_a is surjective. The affine section-map criterion then gives a closed
immersion over this basic open. This includes a = 0, when both opens are empty. -/
theorem isClosedImmersion_restrict_basicOpen_of_localizedMap_surjective
    {X S : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
    (U : S.Opens) (hU : IsAffineOpen U) (a : Γ(S, U))
    (ha : letI := (f.app U).hom.toAlgebra
      Function.Surjective (LocalizedModule.map (Submonoid.powers a)
        (Algebra.linearMap Γ(S, U) Γ(X, f ⁻¹ᵁ U)))) :
    IsClosedImmersion (f ∣_ S.basicOpen a) := by
  let := (f.app U).hom.toAlgebra
  have hV := hU.preimage f
  have := hU.isLocalization_basicOpen a
  have := hV.isLocalization_basicOpen (f.app U a)
  have hmap : Function.Surjective
      (IsLocalization.Away.map Γ(S, S.basicOpen a)
        Γ(X, X.basicOpen (f.app U a)) (f.app U).hom a) :=
    surjective_awayMap_of_localizedMap_surjective a ha
  have happ : Function.Surjective (f.app (S.basicOpen a)) := by
    rw [hU.app_basicOpen_eq_away_map f hV a]
    simp only [CommRingCat.hom_comp, RingHom.coe_comp]
    apply Function.Surjective.comp ?_ hmap
    exact (ConcreteCategory.bijective_of_isIso _).2
  have : IsAffine (S.basicOpen a).toScheme := hU.basicOpen a
  have : IsAffine (f ⁻¹ᵁ S.basicOpen a).toScheme := (hU.basicOpen a).preimage f
  apply IsClosedImmersion.of_surjective_of_isAffine
  rw [morphismRestrict_appTop]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp]
  apply Function.Surjective.comp ?_ ?_
  · exact (ConcreteCategory.bijective_of_isIso _).2
  · change Function.Surjective (f.app ((S.basicOpen a).ι ''ᵁ ⊤)).hom
    rw [Scheme.Opens.ι_image_top]
    exact happ

end AlgebraicGeometry
