/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.SixFunctors.Etale.Derived.Orientation
public import WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing

/-!
# The derived Poincaré pairing of a Tate orientation

For a coefficient ring `Λ` with a Tate twist datum (`AlgebraicGeometry.Etale.HasTateTwist`),
smooth purity (`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`) produces
orientations in the form `γ : Λ_X(d)[2d] ≅ Ra^! Λ_Y`: these are the *Tate orientations*
`AlgebraicGeometry.Etale.TateOrientation`. For `a` smooth of relative dimension `d`, a Tate
orientation is an orientation in the sense of the six-functor formalism
(`AlgebraicGeometry.Etale.TateOrientation.toOrientation`), and the derived Poincaré pairing of
`WeilConjectures.SixFunctors.Etale.Derived.PoincarePairing` specialises to

`β_K : Ra_! K ⊗ᴸ (Ra_*(K^∨(d)))[2d] ⟶ Λ_Y`.

## Main definitions

- `AlgebraicGeometry.Etale.twistedDual`: `K^∨(d)`.
- `AlgebraicGeometry.Etale.TateOrientation`: an isomorphism `Λ_X(d)[2d] ≅ Ra^! Λ_Y`.
- `AlgebraicGeometry.Etale.TateOrientation.toOrientation`: the corresponding orientation.
- `AlgebraicGeometry.Etale.TateOrientation.smoothTrace`,
  `AlgebraicGeometry.Etale.TateOrientation.poincarePairing`: the smooth trace and the derived
  Poincaré pairing of a Tate orientation.

## Main statements

- `AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing`
  (`corollary-degreewise-duality-over-fields`): at finite coefficients, the derived Poincaré pairing
  of a Tate orientation is perfect for `K` dualizable.
- `AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_properPoincarePairing`
  (`theorem-poincare-duality--8`): the same for proper `a`, with `Ra_! ≅ Ra_*`.

The degreewise consequences over a field are in
`WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise`.

## Implementation notes

The orientation is an explicit argument. The blueprint's *normalized* orientation is the one
built in the purity chapter, which the repository does not define yet; the traces and pairings
of this chapter are those of an arbitrary Tate orientation, and are normalized when the
orientation is.

The coefficients are `ModuleCat Λ` for a commutative ring `Λ` with a Tate twist datum. With
`[Finite Λ]` and the exponent of `Λ` invertible on the base, this is the finite stage `A_{E,n}`
of the blueprint; the other stages are discussed in
`WeilConjectures.EtaleCohomology.PoincareDuality.PointPerfect`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}

/-- The *twisted dual* `K^∨(d) = K^∨ ⊗ᴸ Λ_X(d)` of `K ∈ D(X_ét, Λ)`, written with
`AlgebraicGeometry.Etale.derivedTensor`. -/
noncomputable abbrev twistedDual (d : ℕ) (K : DerivedCategoryModule Λ X) :
    DerivedCategoryModule Λ X :=
  ((derivedTensor _ X).obj ((DerivedCategory.coefficientDual _ X).obj (op K))).obj
    (tateObject Λ X d)

/-- A *Tate orientation* of `a : X ⟶ Y` of relative dimension `d`: an isomorphism
`γ : Λ_X(d)[2d] ≅ Ra^! Λ_Y`, the form in which smooth purity
(`AlgebraicGeometry.Etale.nonempty_iso_dualizingComplex_twistShift`) produces orientations. -/
abbrev TateOrientation (a : X ⟶ Y) [HasCompactification a] (d : ℕ) : Type (u + 1) :=
  (twistShift Λ X d).obj (constantComplex Λ X) ≅ dualizingComplex Λ a

namespace TateOrientation

variable {Λ} {a : X ⟶ Y} [HasCompactification a] {d : ℕ}

/-- A Tate orientation `γ : Λ_X(d)[2d] ≅ Ra^! Λ_Y` read as an isomorphism
`Λ_X(d)⟦2d⟧ ≅ ω_X` out of the shifted twist itself: `γ` precomposed with the left unitor
`Λ_X(d) ≅ Λ_X ⊗ᴸ Λ_X(d)`. -/
noncomputable def dualizingComplexIso (γ : TateOrientation Λ a d) :
    (tateObject Λ X d)⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ a :=
  (shiftFunctor _ (2 * d : ℤ)).mapIso (derivedTensorLeftUnitor _ X _).symm ≪≫ γ

/-- A Tate orientation `γ : Λ_X(d)[2d] ≅ Ra^! Λ_Y` of a morphism `a` smooth of relative dimension
`d`, as an orientation in the sense of the six-functor formalism
(`AlgebraicGeometry.Etale.Orientation.ofDualizingComplexIso`): its isomorphism
`Λ_X(d)[2d] ≅ Ra^! Λ_Y` is `γ.dualizingComplexIso`. -/
noncomputable def toOrientation [SmoothOfRelativeDimension d a] (γ : TateOrientation Λ a d) :
    Orientation Λ a d :=
  Orientation.ofDualizingComplexIso γ.dualizingComplexIso

/-- Blueprint `theorem-poincare-duality--6`: The pairing data.

The smooth trace `Tr_γ : Ra_!(Λ_X(d)[2d]) ⟶ Λ_Y` of a Tate orientation
(`AlgebraicGeometry.Etale.smoothTrace`). -/
noncomputable def smoothTrace (γ : TateOrientation Λ a d) :
    (R(a)_![ModuleCat.{u + 1} Λ]).obj ((tateObject Λ X d)⟦(2 * d : ℤ)⟧) ⟶ 𝟙_ _ :=
  Etale.smoothTrace (rightDerivedUpperShriekAdjunction Λ a) γ.dualizingComplexIso

/-- Blueprint `definition-perfect-pairing`: The derived pairing, and perfectness of a pairing.

The derived Poincaré pairing of a Tate orientation `γ`,

`β_K : Ra_! K ⊗ᴸ (Ra_*(K^∨(d)))[2d] ⟶ Λ_Y`

(`AlgebraicGeometry.Etale.poincarePairing`), with `K^∨(d) = K^∨ ⊗ᴸ Λ_X(d)`
(`AlgebraicGeometry.Etale.twistedDual`). -/
noncomputable def poincarePairing (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) :
    ((derivedTensor _ Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)).obj
        (((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦(2 * d : ℤ)⟧) ⟶ 𝟙_ _ :=
  Etale.poincarePairing (rightDerivedUpperShriekAdjunction Λ a) γ.dualizingComplexIso K

/-- Blueprint `theorem-poincare-duality--6`: Derived Poincaré duality, at a finite
coefficient stage `Λ = A`. This is also the derived part of blueprint
`corollary-degreewise-duality-over-fields`.

The derived Poincaré pairing of a Tate orientation is perfect, for a finite coefficient ring
`Λ` and `K` dualizable (`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing`): the
tensor–internal-hom adjoint `RΓ(X, K^∨(d))[2d] ⟶ RΓ_c(X, K)^∨` of
`β_K : RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ` is an isomorphism, read in `D(Y_ét, Λ)`. The integral
stage `Λ = 𝒪_E` is
`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isSepClosed_of_isDualizable`. -/
theorem isPerfectPairing_poincarePairing (γ : TateOrientation Λ a d)
    {K : DerivedCategoryModule Λ X} (hKd : IsDualizable K) :
    IsPerfectPairing (γ.poincarePairing K) :=
  Etale.isPerfectPairing_poincarePairing a Λ _ hKd

/-- The derived Poincaré pairing of a Tate orientation `γ` of a proper morphism `a`, read
through `Ra_! ≅ Ra_*` (`AlgebraicGeometry.Etale.properPoincarePairing`):

`Ra_* K ⊗ᴸ (Ra_*(K^∨(d)))[2d] ⟶ Λ_Y`. -/
noncomputable def properPoincarePairing [IsProper a] (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) :
    ((derivedTensor _ Y).obj ((R((a)_*[ModuleCat.{u + 1} Λ])).obj K)).obj
        (((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦(2 * d : ℤ)⟧) ⟶ 𝟙_ _ :=
  Etale.properPoincarePairing (rightDerivedUpperShriekAdjunction Λ a) γ.dualizingComplexIso K

/-- Blueprint `theorem-poincare-duality--8`: Proper Poincaré duality.

For `a` proper, the derived Poincaré pairing of a Tate orientation read through
`Ra_! ≅ Ra_*`, `RΓ(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ` over `Y = Spec k`, is perfect for a finite
coefficient ring `Λ` and `K` dualizable
(`AlgebraicGeometry.Etale.isPerfectPairing_properPoincarePairing`). -/
theorem isPerfectPairing_properPoincarePairing [IsProper a]
    (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X} (hKd : IsDualizable K) :
    IsPerfectPairing (γ.properPoincarePairing K) :=
  Etale.isPerfectPairing_properPoincarePairing a Λ _ hKd

end TateOrientation

end Etale

end AlgebraicGeometry
