/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.RingTheory.Localization.Away.Basic
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent

/-!
# The universal scheme on which the exponent of a coefficient ring is invertible

Let `Λ` be a commutative ring of positive characteristic `n`. The scheme
`S_Λ = Spec ℤ[1/n]` (`AlgebraicGeometry.invertibleExponentBase`) is terminal among the schemes
on which the exponent of `Λ` is invertible: every such scheme `X` has exactly one morphism to it
(`AlgebraicGeometry.toInvertibleExponentBase`). Objects defined on `S_Λ` and pulled back along
these morphisms are therefore canonically compatible with all pullbacks between such schemes;
this is how the Tate twists are constructed.

## Main definitions

- `AlgebraicGeometry.invertibleExponentBase`: the scheme `Spec ℤ[1/n]`.
- `AlgebraicGeometry.toInvertibleExponentBase`: the morphism `X ⟶ Spec ℤ[1/n]`.

## Main statements

- `AlgebraicGeometry.isUnit_ringChar_of_hasInvertibleExponent`: the characteristic of `Λ` is
  invertible on a scheme on which the exponent of `Λ` is invertible.
- `AlgebraicGeometry.subsingleton_hom_invertibleExponentBase`: there is at most one morphism to
  `Spec ℤ[1/n]`.
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

variable (Λ : Type*) [CommRing Λ]

/-- The ring `ℤ[1/n]`, for `n` the characteristic of `Λ`, lifted to the universe `u`. -/
abbrev InvertibleExponentRing : Type u :=
  ULift.{u} (Localization.Away (ringChar Λ : ℤ))

/-- The scheme `Spec ℤ[1/n]`, for `n` the characteristic of `Λ`: the universal scheme on which
the exponent of `Λ` is invertible. -/
noncomputable abbrev invertibleExponentBase : Scheme.{u} :=
  Spec (CommRingCat.of (InvertibleExponentRing.{u} Λ))

variable {Λ}

/-- If the exponent of `Λ` is invertible on `X`, so is the characteristic of `Λ`: it divides
every integer vanishing in `Λ`. -/
lemma isUnit_ringChar_of_hasInvertibleExponent (X : Scheme.{u}) [HasInvertibleExponent Λ X] :
    IsUnit ((ringChar Λ : ℕ) : Γ(X, ⊤)) := by
  obtain ⟨n, -, hΛ, hu⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := X)
  obtain ⟨c, rfl⟩ := ringChar.dvd hΛ
  rw [Nat.cast_mul] at hu
  exact isUnit_of_mul_isUnit_left hu

/-- The ring homomorphism `ℤ[1/n] ⟶ Γ(X, 𝒪_X)` for a scheme on which the characteristic `n` of
`Λ` is invertible. -/
noncomputable def invertibleExponentRingHom (X : Scheme.{u}) [HasInvertibleExponent Λ X] :
    CommRingCat.of (InvertibleExponentRing.{u} Λ) ⟶ Γ(X, ⊤) :=
  CommRingCat.ofHom ((IsLocalization.Away.lift (ringChar Λ : ℤ)
      (g := Int.castRingHom Γ(X, ⊤))
        (by simpa using isUnit_ringChar_of_hasInvertibleExponent X)).comp
    ULift.ringEquiv.toRingHom)

/-- The morphism `X ⟶ Spec ℤ[1/n]` from a scheme on which the characteristic `n` of `Λ` is
invertible. -/
noncomputable def toInvertibleExponentBase (X : Scheme.{u}) [HasInvertibleExponent Λ X] :
    X ⟶ invertibleExponentBase.{u} Λ :=
  X.toSpecΓ ≫ Spec.map (invertibleExponentRingHom X)

/-- Ring homomorphisms out of `ℤ[1/n]` are unique. -/
lemma invertibleExponentRing_ringHom_ext {A : Type*} [CommRing A]
    (f g : InvertibleExponentRing.{u} Λ →+* A) : f = g := by
  have : f.comp ULift.ringEquiv.symm.toRingHom = g.comp ULift.ringEquiv.symm.toRingHom :=
    IsLocalization.ringHom_ext (Submonoid.powers (ringChar Λ : ℤ)) (RingHom.ext_int _ _)
  ext x
  exact congrArg (fun φ : Localization.Away (ringChar Λ : ℤ) →+* A ↦ φ (ULift.down x)) this

/-- There is at most one morphism to `Spec ℤ[1/n]`. -/
instance subsingleton_hom_invertibleExponentBase (X : Scheme.{u}) :
    Subsingleton (X ⟶ invertibleExponentBase.{u} Λ) := by
  refine ⟨fun f g ↦ ext_of_isAffine ?_⟩
  have h := invertibleExponentRing_ringHom_ext ((Scheme.ΓSpecIso _).inv ≫ f.appTop).hom
    ((Scheme.ΓSpecIso _).inv ≫ g.appTop).hom
  have h' : (Scheme.ΓSpecIso _).inv ≫ f.appTop = (Scheme.ΓSpecIso _).inv ≫ g.appTop :=
    CommRingCat.hom_ext h
  simpa using h'

/-- Any morphism to `Spec ℤ[1/n]` is the canonical one. -/
lemma eq_toInvertibleExponentBase {X : Scheme.{u}} [HasInvertibleExponent Λ X]
    (f : X ⟶ invertibleExponentBase.{u} Λ) : f = toInvertibleExponentBase X :=
  Subsingleton.elim _ _


/-- The canonical morphisms to `Spec ℤ[1/n]` are compatible with all morphisms. -/
@[reassoc (attr := simp)]
lemma comp_toInvertibleExponentBase {X Y : Scheme.{u}} [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) :
    f ≫ toInvertibleExponentBase Y = toInvertibleExponentBase (Λ := Λ) X :=
  Subsingleton.elim _ _

end AlgebraicGeometry
