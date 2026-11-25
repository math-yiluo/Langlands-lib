/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalDuality

/-!
# Where Poincaré duality feeds

The pointer remarks `sk-rem-feeds` and `rem-feeds` of the blueprint record that global duality
and the identification of the derived Poincaré pairing with the duality isomorphism are cited
directly from the six-functor formalism, that their degreewise consequence over a field is
degreewise duality, and that the `p`-primary case in characteristic `p` is excluded throughout by
`ℓ ≠ p`. This file packages the cited results, over a separably closed field `k` and a finite
field of coefficients `Λ` whose characteristic `ℓ` is invertible on `X`
(`AlgebraicGeometry.HasInvertibleExponent`, the hypothesis `ℓ ≠ p`).

## Main statements

- `AlgebraicGeometry.Etale.TateOrientation.globalDuality_and_identification_and_degreewiseDuality`
  (`sk-rem-feeds`).
- `AlgebraicGeometry.Etale.TateOrientation.globalDuality_and_isPerfectPairing_and_degreewiseDuality`
  (`rem-feeds`).
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale.TateOrientation

variable {k : Type u} [Field k] [IsSepClosed k] {Λ : Type (u + 1)} [CommRing Λ] [IsDomain Λ]
  [Finite Λ] [HasTateTwist Λ] {X : Scheme.{u}} {a : X ⟶ Spec (.of k)} [HasCompactification a]
  [LocallyOfFiniteType a] {d : ℕ}

/-- Blueprint `sk-rem-feeds`: Where this feeds, and what remains.

Let `k` be separably closed, `Λ` a finite field whose characteristic `ℓ` is invertible on `X`
(so `ℓ ≠ p`: the `p`-primary case in characteristic `p` is excluded), `a : X ⟶ Spec k` smooth of
relative dimension `d` with a Tate orientation `γ`, and `K ∈ D^b_{ctf}(X, Λ)` perfect. Then:

1. global duality `RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)` holds (`theorem-global-verdier-duality`,
   `AlgebraicGeometry.Etale.nonempty_iso_coefficientDual_rightDerivedLowerShriek`);
2. the duality isomorphism `RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨` of the identification holds
   (`theorem-poincare-duality--7`,
   `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedLowerStar_coefficientDual_of_orientation`);
3. its degreewise consequence over the field `Λ`, `H^{2d-i}(X, K^∨(d)) ≅ H^i_c(X, K)^∨` with
   both sides finite-dimensional, holds (`corollary-degreewise-duality-over-fields`,
   `AlgebraicGeometry.Etale.TateOrientation.degreewise_duality`). -/
theorem globalDuality_and_identification_and_degreewiseDuality [HasInvertibleExponent Λ X]
    [SmoothOfRelativeDimension d a] (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) (hKd : IsDualizable K) :
    Nonempty ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
        (op ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)) ≅
      (R((a)_*[ModuleCat.{u + 1} Λ])).obj ((verdierDual Λ a).obj (op K))) ∧
    Nonempty (((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦(2 * d : ℤ)⟧ ≅
      (DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
        (op ((R(a)_![ModuleCat.{u + 1} Λ]).obj K))) ∧
    ∀ i : ℤ, Module.Finite Λ ((H_c(a)[ModuleCat.{u + 1} Λ](i)).obj K) ∧
      Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (2 * d - i)).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj (twistedDual Λ d K))) ∧
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (2 * d - i)).obj
          ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj (twistedDual Λ d K)) ≅
        ModuleCat.of Λ (Module.Dual Λ ((H_c(a)[ModuleCat.{u + 1} Λ](i)).obj K))) :=
  ⟨nonempty_iso_coefficientDual_rightDerivedLowerShriek Λ a K,
    nonempty_iso_rightDerivedLowerStar_coefficientDual_of_orientation Λ a γ.toOrientation hKd,
    fun i ↦ γ.degreewise_duality hK hKd i⟩

/-- Blueprint `rem-feeds`: Where this feeds, and what remains.

Let `k` be separably closed, `Λ` a finite field whose characteristic `ℓ` is invertible on `X`
(so `ℓ ≠ p`: the `p`-primary case in characteristic `p` is excluded), `γ` a Tate orientation of
`a : X ⟶ Spec k` of relative dimension `d`, and `K ∈ D^b_{ctf}(X, Λ)` perfect. Then:

1. global duality `RΓ_c(X, K)^∨ ≅ RΓ(X, 𝔻_X K)` holds (`theorem-global-verdier-duality`,
   `AlgebraicGeometry.Etale.nonempty_iso_coefficientDual_rightDerivedLowerShriek`);
2. the derived Poincaré pairing `β_K : RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ` is perfect
   (`theorem-poincare-duality--7`,
   `AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing`);
3. its degreewise consequence over the field `Λ`, `H^{2d-i}(X, K^∨(d)) ≅ H^i_c(X, K)^∨` with
   both sides finite-dimensional, holds (`corollary-degreewise-duality-over-fields--1`, at the
   étale field stage of a finite field, in non-canonical form,
   `AlgebraicGeometry.Etale.TateOrientation.degreewise_duality`). -/
theorem globalDuality_and_isPerfectPairing_and_degreewiseDuality [HasInvertibleExponent Λ X]
    (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K) (hKd : IsDualizable K) :
    Nonempty ((DerivedCategory.coefficientDual (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
        (op ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)) ≅
      (R((a)_*[ModuleCat.{u + 1} Λ])).obj ((verdierDual Λ a).obj (op K))) ∧
    IsPerfectPairing (γ.poincarePairing K) ∧
    ∀ i : ℤ, Module.Finite Λ ((H_c(a)[ModuleCat.{u + 1} Λ](i)).obj K) ∧
      Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (2 * d - i)).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj (twistedDual Λ d K))) ∧
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (2 * d - i)).obj
          ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj (twistedDual Λ d K)) ≅
        ModuleCat.of Λ (Module.Dual Λ ((H_c(a)[ModuleCat.{u + 1} Λ](i)).obj K))) :=
  ⟨nonempty_iso_coefficientDual_rightDerivedLowerShriek Λ a K,
    γ.isPerfectPairing_poincarePairing hKd, fun i ↦ γ.degreewise_duality hK hKd i⟩

end AlgebraicGeometry.Etale.TateOrientation
