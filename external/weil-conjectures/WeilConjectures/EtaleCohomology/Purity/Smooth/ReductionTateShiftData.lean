/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.DiagonalOrientationReductionSupports
public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerProductBaseChange
public import WeilConjectures.EtaleCohomology.TateTwist.Basic

/-!
# Tate shift data of the reduction of coefficients pulled back from a base

Let `ρ : Λ →+* Λ'` be a surjective morphism of commutative rings with principal kernel and
`Ψ = - ⊗ᴸ_Λ Λ'` the derived extension of scalars
(`AlgebraicGeometry.Etale.derivedExtendScalars`). A family of identifications
`c_m : Ψ(Λ_S(m)[2m]) ≅ Λ'_S(m)[2m]` on a single scheme `S`, pulled back along morphisms
`t : X ⟶ S` through the commutation of `Ψ` with `Lt^*`, gives identifications
`Ψ(Λ_X(m)[2m]) ≅ Λ'_X(m)[2m]` (`AlgebraicGeometry.Etale.derivedExtendScalarsTateShiftIsoOfPullback`)
compatible with the derived pullbacks
(`AlgebraicGeometry.Etale.derivedExtendScalarsTateShiftIsoOfPullback_hom_pullback`). Taking for
`S` the universal base `Spec ℤ[1/n]` on which the characteristic `n` of `Λ` is invertible, this
is a Tate shift datum of `Ψ` (`AlgebraicGeometry.Etale.DerivedExtendScalarsTateShiftData.ofBase`,
blueprint `proposition-compatibility-purity-change-coefficients`).
-/

@[expose] public section

universe u

open CategoryTheory Limits

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

/-- If the exponent of `Λ` is invertible on `X`, so is the exponent of every `Λ`-algebra `Λ'`. -/
lemma HasInvertibleExponent.of_ringHom {Λ Λ' : Type*} [CommRing Λ] [CommRing Λ'] (ρ : Λ →+* Λ')
    (X : Scheme.{u}) [HasInvertibleExponent Λ X] : HasInvertibleExponent Λ' X := by
  obtain ⟨n, hn, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := X)
  exact ⟨n, hn, by rw [← map_natCast ρ, hΛ, map_zero], hu⟩

open Scheme

namespace Etale

/-- The characteristic `n ≠ 0` of `Λ` is invertible on `Spec ℤ[1/n]`. -/
instance hasInvertibleExponent_invertibleExponentBase (Λ : Type (u + 1)) [CommRing Λ]
    [NeZero (ringChar Λ)] : HasInvertibleExponent Λ (invertibleExponentBase.{u} Λ) :=
  ⟨ringChar Λ, Nat.pos_of_ne_zero (NeZero.ne _), ringChar.Nat.cast_ringChar, by
    simpa using (isUnit_ringChar_invertibleExponentRing Λ).map
      (Scheme.ΓSpecIso (CommRingCat.of (InvertibleExponentRing.{u} Λ))).inv.hom⟩

set_option hygiene false in
/-- The derived category `D(X_ét, Λ)` of étale sheaves of `Λ`-modules on `X`. -/
local notation "𝐃(" X ", " Λ ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) (ModuleCat.{u + 1} Λ))

variable {Λ Λ' : Type (u + 1)} [CommRing Λ] [CommRing Λ'] {ρ : Λ →+* Λ'} {a : Λ}
  (hρ : Function.Surjective ρ) (ha : RingHom.ker ρ = Ideal.span {a})
  [HasTateTwist Λ] [HasTateTwist Λ']

section OfPullback

variable {S : Scheme.{u}} [HasInvertibleExponent Λ S] [HasInvertibleExponent Λ' S]
  (c : ∀ m : ℤ, (derivedExtendScalars hρ ha S).obj ((tateObject Λ S m)⟦2 * m⟧) ≅
    (tateObject Λ' S m)⟦2 * m⟧)

/-- The identification `Ψ(Λ_X(m)[2m]) ≅ Λ'_X(m)[2m]` pulled back along `t : X ⟶ S` from a family
of identifications `c_m : Ψ(Λ_S(m)[2m]) ≅ Λ'_S(m)[2m]`:
`Ψ(Λ_X(m)[2m]) ≅ Ψ Lt^*(Λ_S(m)[2m]) ≅ Lt^* Ψ(Λ_S(m)[2m]) ≅ Lt^*(Λ'_S(m)[2m]) ≅ Λ'_X(m)[2m]`. -/
noncomputable def derivedExtendScalarsTateShiftIsoOfPullback {X : Scheme.{u}}
    [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ' X] (t : X ⟶ S) (m : ℤ) :
    (derivedExtendScalars hρ ha X).obj ((tateObject Λ X m)⟦2 * m⟧) ≅
      (tateObject Λ' X m)⟦2 * m⟧ :=
  (derivedExtendScalars hρ ha X).mapIso (leftDerivedUpperStarTateShiftIso Λ t m).symm ≪≫
    (derivedExtendScalarsPullbackIso hρ ha t).app _ ≪≫
      (L((t)^*[ModuleCat.{u + 1} Λ'])).mapIso (c m) ≪≫ leftDerivedUpperStarTateShiftIso Λ' t m

/-- The identifications `Ψ(Λ(m)[2m]) ≅ Λ'(m)[2m]` pulled back from `S` are compatible with the
derived pullbacks: for `tU = e ≫ tX`, the square
```
Ψ Le^*(Λ_X(m)[2m]) ──Ψ(≅)──▶ Ψ(Λ_U(m)[2m])
        │ ≅                          │ ≅
        ▼                            ▼
Le^* Ψ(Λ_X(m)[2m]) ──≅──▶ Le^*(Λ'_X(m)[2m]) ──≅──▶ Λ'_U(m)[2m]
```
commutes. -/
lemma derivedExtendScalarsTateShiftIsoOfPullback_hom_pullback {U X : Scheme.{u}}
    [HasInvertibleExponent Λ U] [HasInvertibleExponent Λ' U] [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ' X] (e : U ⟶ X) (tU : U ⟶ S) (tX : X ⟶ S) (h : tU = e ≫ tX)
    (m : ℤ) :
    (derivedExtendScalars hρ ha U).map (leftDerivedUpperStarTateShiftIso Λ e m).hom ≫
        (derivedExtendScalarsTateShiftIsoOfPullback hρ ha c tU m).hom =
      (derivedExtendScalarsPullbackIso hρ ha e).hom.app _ ≫
        (L((e)^*[ModuleCat.{u + 1} Λ'])).map
          (derivedExtendScalarsTateShiftIsoOfPullback hρ ha c tX m).hom ≫
          (leftDerivedUpperStarTateShiftIso Λ' e m).hom := by
  have hΛ := leftDerivedUpperStarTateShiftIso_comp (Λ := Λ) e tX tU h m
  have hΛ' := leftDerivedUpperStarTateShiftIso_comp (Λ := Λ') e tX tU h m
  have hp := derivedExtendScalarsPullbackMap_comp hρ ha e tX tU h ((tateObject Λ S m)⟦2 * m⟧)
  have hn₁ := (derivedExtendScalarsPullbackMap hρ ha e).naturality
    (leftDerivedUpperStarTateShiftIso Λ tX m).inv
  have hn₂ := (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ') e tX tU h).inv.naturality (c m).hom
  simp only [Functor.comp_obj, Functor.comp_map] at hn₁ hn₂
  have hp' : (derivedExtendScalars hρ ha U).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) e tX tU h).inv.app
        ((tateObject Λ S m)⟦2 * m⟧)) ≫
        (derivedExtendScalarsPullbackMap hρ ha tU).app ((tateObject Λ S m)⟦2 * m⟧) =
      (derivedExtendScalarsPullbackMap hρ ha e).app _ ≫
        (L((e)^*[ModuleCat.{u + 1} Λ'])).map
          ((derivedExtendScalarsPullbackMap hρ ha tX).app ((tateObject Λ S m)⟦2 * m⟧)) ≫
        (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ') e tX tU h).inv.app _ := by
    rw [← cancel_epi ((derivedExtendScalars hρ ha U).map
      ((leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) e tX tU h).hom.app _)),
      ← Functor.map_comp_assoc, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id,
      Category.id_comp, reassoc_of% hp, Iso.hom_inv_id_app, Category.comp_id]
  simp only [derivedExtendScalarsTateShiftIsoOfPullback, hΛ, hΛ', Iso.trans_hom,
    Iso.symm_hom, Iso.trans_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom,
    Functor.mapIso_inv, derivedExtendScalarsPullbackIso_hom, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id, Category.id_comp,
    reassoc_of% hp', ← reassoc_of% hn₂, Iso.inv_hom_id_app_assoc, reassoc_of% hn₁]

end OfPullback

section Base

variable [NeZero (ringChar Λ)]
  (c : ∀ m : ℤ, (derivedExtendScalars hρ ha (invertibleExponentBase.{u} Λ)).obj
    ((tateObject Λ (invertibleExponentBase.{u} Λ) m)⟦2 * m⟧) ≅
      (tateObject Λ' (invertibleExponentBase.{u} Λ) m)⟦2 * m⟧)

/-- Blueprint `proposition-compatibility-purity-change-coefficients`

**The Tate shift datum of the reduction of coefficients pulled back from the universal base.**
A family of identifications `c_m : Ψ(Λ_S(m)[2m]) ≅ Λ'_S(m)[2m]` on `S = Spec ℤ[1/n]`, `n` the
characteristic of `Λ`, pulled back along the unique morphisms `X ⟶ S`
(`AlgebraicGeometry.toInvertibleExponentBase`), is a Tate shift datum of `Ψ`: the compatibility
with the derived pullbacks is
`AlgebraicGeometry.Etale.derivedExtendScalarsTateShiftIsoOfPullback_hom_pullback`. -/
noncomputable def DerivedExtendScalarsTateShiftData.ofBase :
    DerivedExtendScalarsTateShiftData Λ Λ' hρ ha :=
  haveI := HasInvertibleExponent.of_ringHom ρ (invertibleExponentBase.{u} Λ)
  { iso X _ _ m := derivedExtendScalarsTateShiftIsoOfPullback hρ ha c
      (toInvertibleExponentBase (Λ := Λ) X) m
    map_leftDerivedUpperStarTateShiftIso e m :=
      derivedExtendScalarsTateShiftIsoOfPullback_hom_pullback hρ ha c e _ _
        (comp_toInvertibleExponentBase e).symm m }

end Base

end Etale

end AlgebraicGeometry
