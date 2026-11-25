/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance

/-!
# Frobenius: reciprocity

Part (b) of `theorem-poincare-duality-frobenius`. Over a field, if the line-valued Poincaré pairing
is perfect, `F_{K^∨}` is conjugate to `q^d (F_{c,K}^{-1})^t`, so the eigenvalues of `F` on
`H^{2d-i}(X, K^∨)` are the `q^d / α` for the eigenvalues `α` of `F` on `H^i_c(X, K)`, with
multiplicities.

## Main statements

- `AlgebraicGeometry.Etale.TateOrientation.conj_frobeniusOperator_eq_smul_inverse_dualMap`,
  `AlgebraicGeometry.Etale.TateOrientation.roots_map_charpoly_frobeniusOperator`
  (`theorem-poincare-duality-frobenius--6`, `theorem-poincare-duality-frobenius` (b)): conjugacy and
  reciprocal eigenvalues.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

namespace TateOrientation

section Reciprocity

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y}
  [HasCompactification a] [QuasiCompact a] {d : ℕ} {g : X ⟶ X} {h : Y ⟶ Y}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

/-- Blueprint `theorem-poincare-duality-frobenius--6`: Reciprocal eigenvalues.

**The Frobenius of the dual is conjugate to `q^d` times the inverse transpose.** If `Λ` is a
field, then with the hypotheses of
`AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePoincarePairing_frobeniusOperator`,
`q` invertible in `Λ`, and the line-valued pairing
`H^i_c(X, K) × H^{2d-i}(X, K^∨) ⟶ Λ(-d) ≃ Λ` perfect (for a trivialisation `ℓ` of the value
line; at a field stage this is `corollary-degreewise-duality-over-fields--1`), the adjoint
`Φ : H^{2d-i}(X, K^∨) ≃ H^i_c(X, K)^∨` of the pairing satisfies

`Φ ∘ F_{K^∨} ∘ Φ⁻¹ = q^d (F_{c,K}^{-1})^t`.

In particular `F_{c,K}` is invertible (`Ring.inverse` is its inverse transpose). -/
theorem conj_frobeniusOperator_eq_smul_inverse_dualMap (sq : IsPullback g a a h)
    (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.coefficientDual _ X).obj (op K)) ⟶
      (DerivedCategory.coefficientDual _ X).obj (op K))
    (hψ : IsWeilPairing g φ ψ (leftDerivedUpperStarUnitIso _ g).hom
      (DerivedCategory.coefficientEvaluation K))
    (τ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ Y (-d)) ⟶ tateObject Λ Y (-d))
    (hTr : IsWeilMorphism h
      (shiftWeilDatum h (lowerShriekWeilDatum sq (leftDerivedUpperStarUnitIso _ g).hom) (2 * d))
      τ γ.untwistedSmoothTrace)
    (q : ℕ) (hτ : ∀ z, frobeniusOperator h τ z = ((q : Λ) ^ d) • z) (hΛ : IsField Λ)
    (hq : (q : Λ) ≠ 0) (i j : ℤ) (hij : i + j = 2 * d)
    (ℓ : (𝟙_ (DerivedCategoryModule Λ Y) ⟶ tateObject Λ Y (-d)) ≃ₗ[Λ] Λ)
    [((γ.untwistedDegreewisePoincarePairing K i j hij).compr₂ ℓ.toLinearMap).IsPerfPair] :
    ((γ.untwistedDegreewisePoincarePairing K i j hij).compr₂ ℓ.toLinearMap).flip.toPerfPair.conj
        (frobeniusOperator h (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) j)) =
      ((q : Λ) ^ d) •
        Ring.inverse
          (frobeniusOperator h (shiftWeilDatum h (lowerShriekWeilDatum sq φ) i)).dualMap := by
  refine LinearMap.conj_toPerfPair_eq_smul_inverse_dualMap_of_similitude_of_isField hΛ
    (by have := hΛ.isDomain; exact pow_ne_zero _ hq) fun x y ↦ ?_
  rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply,
    untwistedDegreewisePoincarePairing_frobeniusOperator sq γ φ ψ hψ τ hTr q hτ, map_smul,
    smul_eq_mul]

/-- Blueprint `theorem-poincare-duality-frobenius--6`: Reciprocal eigenvalues.

**Reciprocal eigenvalues.** With the hypotheses of
`AlgebraicGeometry.Etale.TateOrientation.conj_frobeniusOperator_eq_smul_inverse_dualMap`, the
eigenvalues of `F_{K^∨}` on `H^{2d-i}(X, K^∨)`, computed in an algebraically closed field `M`
containing `Λ` and counted with algebraic multiplicity, are the `q^d / α` for the eigenvalues
`α` of `F_{c,K}` on `H^i_c(X, K)`. The finiteness and freeness of the two spaces, needed to
speak of characteristic polynomials, also follow from the perfectness of the pairing over the
field `Λ`. -/
theorem roots_map_charpoly_frobeniusOperator (sq : IsPullback g a a h)
    (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.coefficientDual _ X).obj (op K)) ⟶
      (DerivedCategory.coefficientDual _ X).obj (op K))
    (hψ : IsWeilPairing g φ ψ (leftDerivedUpperStarUnitIso _ g).hom
      (DerivedCategory.coefficientEvaluation K))
    (τ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ Y (-d)) ⟶ tateObject Λ Y (-d))
    (hTr : IsWeilMorphism h
      (shiftWeilDatum h (lowerShriekWeilDatum sq (leftDerivedUpperStarUnitIso _ g).hom) (2 * d))
      τ γ.untwistedSmoothTrace)
    (q : ℕ) (hτ : ∀ z, frobeniusOperator h τ z = ((q : Λ) ^ d) • z) (hΛ : IsField Λ)
    (hq : (q : Λ) ≠ 0) (i j : ℤ) (hij : i + j = 2 * d)
    (ℓ : (𝟙_ (DerivedCategoryModule Λ Y) ⟶ tateObject Λ Y (-d)) ≃ₗ[Λ] Λ)
    [((γ.untwistedDegreewisePoincarePairing K i j hij).compr₂ ℓ.toLinearMap).IsPerfPair]
    [Module.Free Λ
      (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)]
    [Module.Finite Λ
      (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)]
    [Module.Free Λ (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
      ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦j⟧)]
    [Module.Finite Λ (𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
      ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦j⟧)]
    {M : Type*} [Field M] [IsAlgClosed M] (ι : Λ →+* M) :
    ((frobeniusOperator h (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) j)).charpoly.map
        ι).roots =
      ((frobeniusOperator h (shiftWeilDatum h (lowerShriekWeilDatum sq φ) i)).charpoly.map
        ι).roots.map fun z ↦ ι ((q : Λ) ^ d) / z :=
  LinearMap.roots_map_charpoly_of_similitude_of_isField
    (p := (γ.untwistedDegreewisePoincarePairing K i j hij).compr₂ ℓ.toLinearMap) hΛ
    (by have := hΛ.isDomain; exact pow_ne_zero _ hq) (fun x y ↦ by
      rw [LinearMap.compr₂_apply, LinearMap.compr₂_apply,
        untwistedDegreewisePoincarePairing_frobeniusOperator sq γ φ ψ hψ τ hTr q hτ, map_smul,
        smul_eq_mul]) ι

end Reciprocity

end TateOrientation

end Etale

end AlgebraicGeometry
