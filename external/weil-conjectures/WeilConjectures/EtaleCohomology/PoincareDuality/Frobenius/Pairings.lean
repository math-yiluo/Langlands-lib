/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobenius
public import WeilConjectures.ZetaLinearAlgebra.Pairing

/-!
# Frobenius: the pairings

Let `a : X ⟶ Y` admit a compactification and `γ : Λ_X(d)[2d] ≅ Ra^! Λ_Y` be a Tate orientation.
This file shows that a Weil pairing compatible with the trace is a morphism of Weil objects
in general, and defines the degreewise Poincaré pairing
`⟨-, -⟩_i : H^i_c(X, K) × H^{2d-i}(X, K^∨(d)) ⟶ Λ` and its untwisted, line-valued form
`H^i_c(X, K) × H^{2d-i}(X, K^∨) ⟶ Λ(-d)`, whose Frobenius equivariance is proved in
`WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance`.

## Main definitions

- `AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing`
  (`corollary-degreewise-duality-over-fields--1`): `⟨-, -⟩_i`.
- `AlgebraicGeometry.Etale.TateOrientation.untwistedPoincarePairing`,
  `AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePoincarePairing`
  (`corollary-degreewise-duality-over-fields--1`): the untwisted pairing
  `Ra_! K ⊗ᴸ (Ra_* K^∨)[2d] ⟶ Λ_Y(-d)` and its degreewise form.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Generic

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}} {a : X ⟶ Y}
  [HasCompactification a] [QuasiCompact a] {d : ℕ} {g : X ⟶ X} {h : Y ⟶ Y}

/-- Blueprint `theorem-poincare-duality-frobenius`: Frobenius: equivariance, similitudine,
reciprocity (a).

**The derived Poincaré pairing of a purity isomorphism is a morphism of Weil objects**: the
form of `AlgebraicGeometry.Etale.TateOrientation.isWeilPairing_poincarePairing` for a purity
isomorphism `γ : T[2d] ≅ ω_X`, a Weil datum `τ` on `T`, and the pairing
`AlgebraicGeometry.Etale.poincarePairing`. -/
theorem isWeilPairing_poincarePairing (sq : IsPullback g a a h)
    {T : DerivedCategoryModule Λ X}
    (γ : T⟦(2 * d : ℤ)⟧ ≅ dualizingComplex Λ a) {K : DerivedCategoryModule Λ X}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (τ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj T ⟶ T)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (((derivedTensor _ X).obj
        ((DerivedCategory.coefficientDual _ X).obj (op K))).obj T) ⟶
      ((derivedTensor _ X).obj ((DerivedCategory.coefficientDual _ X).obj (op K))).obj T)
    (hψ : IsWeilPairing g φ ψ τ (twistedEvaluation T K))
    (hTr : IsWeilMorphism h (lowerShriekWeilDatum sq (shiftWeilDatum g τ (2 * d)))
      (leftDerivedUpperStarUnitIso _ h).hom
        (smoothTrace (rightDerivedUpperShriekAdjunction Λ a) γ)) :
    IsWeilPairing h (lowerShriekWeilDatum sq φ)
      (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) (2 * d))
      (leftDerivedUpperStarUnitIso _ h).hom
      (poincarePairing (rightDerivedUpperShriekAdjunction Λ a) γ K) := by
  have h1 := ((isWeilPairing_mixedSupportCupProduct sq φ ψ).comp
    (hψ.rightDerivedLowerShriek_map sq)).shift_right (2 * d)
  refine ((h1.comp (isWeilMorphism_rightDerivedLowerShriek_commShiftIso_inv sq τ
    (2 * d))).comp hTr).of_eq ?_
  simp only [poincarePairing, poincarePairingEvaluation, Category.assoc]

/-- **The pairing of a Frobenius-equivariant trace is a morphism of Weil objects.** Let `φ` be a
Weil datum on `K`, `ψ` the contragredient datum on `K^∨`, characterised by the Frobenius
equivariance of the evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X`, and `t : (Ra_! Λ_X)[n] ⟶ T` a morphism of Weil
objects for a Weil datum `τ` on `T`. Then the pairing of `t`
(`AlgebraicGeometry.Etale.poincarePairingOfTrace`) is a morphism of Weil objects for the data
`φ_{c,K}`, `φ_{K^∨}[n]` and `τ`. -/
theorem isWeilPairing_poincarePairingOfTrace (sq : IsPullback g a a h)
    {K : DerivedCategoryModule Λ X} (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.coefficientDual _ X).obj (op K)) ⟶
      (DerivedCategory.coefficientDual _ X).obj (op K))
    (hψ : IsWeilPairing g φ ψ (leftDerivedUpperStarUnitIso _ g).hom
      (DerivedCategory.coefficientEvaluation K)) {T : DerivedCategoryModule Λ Y} (n : ℤ)
    (t : ((R(a)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ _))⟦n⟧ ⟶ T)
    (τ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj T ⟶ T)
    (ht : IsWeilMorphism h
      (shiftWeilDatum h (lowerShriekWeilDatum sq (leftDerivedUpperStarUnitIso _ g).hom) n) τ t) :
    IsWeilPairing h (lowerShriekWeilDatum sq φ)
      (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) n) τ
      (poincarePairingOfTrace a K n t) :=
  (((isWeilPairing_mixedSupportCupProduct sq φ ψ).comp
    (hψ.rightDerivedLowerShriek_map sq)).shift_right n).comp ht

end Generic

namespace TateOrientation

section Pairings

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y}
  [HasCompactification a] {d : ℕ}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

omit [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] in
/-- Blueprint `corollary-degreewise-duality-over-fields--1`: Degree of the pairing.

The *degreewise Poincaré pairing* of a Tate orientation `γ`, for `i + j = 2d`,

`⟨-, -⟩_i : H^i_c(X, K) × H^j(X, K^∨(d)) ⟶ Λ`,

with `H^i_c(X, K) = Hom(Λ_Y, (Ra_! K)[i])`, `H^j(X, K^∨(d)) = Hom(Λ_Y, (Ra_* K^∨(d))[j])` and
`Λ = End(Λ_Y)` (for `Y = Spec k`): the degreewise pairing
(`AlgebraicGeometry.Etale.degreewisePairing`) of the derived Poincaré pairing `β_K` in degrees
`i` and `j - 2d`, read through `(Ra_* K^∨(d))[j] ≅ ((Ra_* K^∨(d))[2d])[j - 2d]` and
`Λ_Y[i + (j - 2d)] ≅ Λ_Y`. -/
noncomputable def degreewisePoincarePairing (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d) :
    (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧) →ₗ[Λ]
      (𝟙_ (DerivedCategoryModule Λ Y) ⟶
        ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦j⟧) →ₗ[Λ]
          (𝟙_ (DerivedCategoryModule Λ Y) ⟶ 𝟙_ (DerivedCategoryModule Λ Y)) :=
  ((degreewisePairing (γ.poincarePairing K) i (j - 2 * d)).compl₂
    (Linear.rightComp Λ _ ((shiftFunctorAdd' (DerivedCategoryModule Λ Y) (2 * d : ℤ) (j - 2 * d) j
      (by omega)).hom.app _))).compr₂
    (Linear.rightComp Λ _ ((shiftFunctorZero' (DerivedCategoryModule Λ Y) (i + (j - 2 * d))
      (by omega)).hom.app _))

omit [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] in
lemma degreewisePoincarePairing_apply (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)
    (y : 𝟙_ (DerivedCategoryModule Λ Y) ⟶
      ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦j⟧) :
    γ.degreewisePoincarePairing K i j hij x y =
      degreewisePairing (γ.poincarePairing K) i (j - 2 * d) x
          (y ≫ (shiftFunctorAdd' (DerivedCategoryModule Λ Y) (2 * d : ℤ) (j - 2 * d) j
            (by omega)).hom.app _) ≫
        (shiftFunctorZero' (DerivedCategoryModule Λ Y) (i + (j - 2 * d)) (by omega)).hom.app _ :=
  rfl

/-- Blueprint `corollary-degreewise-duality-over-fields--1`: Degree of the pairing.

The *untwisted derived Poincaré pairing* of a Tate orientation `γ`,

`β_K^{untw} : Ra_! K ⊗ᴸ (Ra_* K^∨)[2d] ⟶ Λ_Y(-d)`,

that is `RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨)[2d] ⟶ Λ(-d)`: the shift is moved out, then come the
mixed-support cup product, `Ra_!` of the evaluation `ev_K : K ⊗ᴸ K^∨ ⟶ Λ_X` and the untwisted
smooth trace `(Ra_! Λ_X)[2d] ⟶ Λ_Y(-d)`
(`AlgebraicGeometry.Etale.TateOrientation.untwistedSmoothTrace`), which eliminates the twist
`Λ_X(d)` of `β_K` through `Λ_Y(d) ⊗ᴸ Λ_Y(-d) ≅ Λ_Y`; this is
`AlgebraicGeometry.Etale.poincarePairingOfTrace` for the untwisted smooth trace. -/
noncomputable def untwistedPoincarePairing (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) :
    ((derivedTensor _ Y).obj ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)).obj
        (((R((a)_*[ModuleCat.{u + 1} Λ])).obj
          ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦(2 * d : ℤ)⟧) ⟶
      tateObject Λ Y (-d) :=
  poincarePairingOfTrace a K (2 * d : ℤ) γ.untwistedSmoothTrace

/-- Blueprint `corollary-degreewise-duality-over-fields--1`: Degree of the pairing.

The *untwisted degreewise Poincaré pairing* of a Tate orientation `γ`, for `i + j = 2d`, the
line-valued pairing

`⟨-, -⟩^{untw}_i : H^i_c(X, K) × H^j(X, K^∨) ⟶ Λ(-d)`,

with `Λ(-d) = Hom(Λ_Y, Λ_Y(-d))` for `Y = Spec k`: the degreewise pairing of the untwisted
derived pairing (`AlgebraicGeometry.Etale.TateOrientation.untwistedPoincarePairing`), read as
in `AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing`. -/
noncomputable def untwistedDegreewisePoincarePairing (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d) :
    (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧) →ₗ[Λ]
      (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦j⟧) →ₗ[Λ]
          (𝟙_ (DerivedCategoryModule Λ Y) ⟶ tateObject Λ Y (-d)) :=
  ((degreewisePairing (γ.untwistedPoincarePairing K) i (j - 2 * d)).compl₂
    (Linear.rightComp Λ _ ((shiftFunctorAdd' (DerivedCategoryModule Λ Y) (2 * d : ℤ) (j - 2 * d) j
      (by omega)).hom.app _))).compr₂
    (Linear.rightComp Λ _ ((shiftFunctorZero' (DerivedCategoryModule Λ Y) (i + (j - 2 * d))
      (by omega)).hom.app _))

lemma untwistedDegreewisePoincarePairing_apply (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)
    (y : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
      ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦j⟧) :
    γ.untwistedDegreewisePoincarePairing K i j hij x y =
      degreewisePairing (γ.untwistedPoincarePairing K) i (j - 2 * d) x
          (y ≫ (shiftFunctorAdd' (DerivedCategoryModule Λ Y) (2 * d : ℤ) (j - 2 * d) j
            (by omega)).hom.app _) ≫
        (shiftFunctorZero' (DerivedCategoryModule Λ Y) (i + (j - 2 * d)) (by omega)).hom.app _ :=
  rfl

end Pairings

end TateOrientation

end Etale

end AlgebraicGeometry
