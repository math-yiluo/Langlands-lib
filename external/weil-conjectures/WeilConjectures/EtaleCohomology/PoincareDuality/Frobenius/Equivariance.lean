/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Pairings

/-!
# Frobenius: equivariance and similitude

Part (a) of `theorem-poincare-duality-frobenius`: the derived Poincaré pairing `β_K` is a morphism
of Weil objects, so the degreewise pairing satisfies `⟨F_{c,K} x, F_{K^∨(d)} y⟩_i = ⟨x, y⟩_i`, and
the untwisted, line-valued pairing satisfies
`⟨F_{c,K} x, F_{K^∨} y⟩^{untw}_i = q^d ⟨x, y⟩^{untw}_i`.

## Main statements

- `AlgebraicGeometry.Etale.TateOrientation.isWeilPairing_poincarePairing`,
  `AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing_frobeniusOperator`
  (`theorem-poincare-duality-frobenius` (a)): `β_K` is a morphism of Weil objects, and the
  degreewise pairing is Frobenius invariant.
- `AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing_frobeniusOperator_eq`
  (`theorem-poincare-duality-frobenius--3`): `⟨F_{c,K} x, F_{K^∨(d)} y⟩_i = ⟨x, y⟩_i`.
- `AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePoincarePairing_frobeniusOperator`
  (`theorem-poincare-duality-frobenius--4`): the untwisted similitude with factor `q^d`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

namespace TateOrientation

section Equivariance

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y}
  [HasCompactification a] [QuasiCompact a] {d : ℕ} {g : X ⟶ X} {h : Y ⟶ Y}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

omit [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] in
/-- Blueprint `theorem-poincare-duality-frobenius`: Frobenius: equivariance, similitudine,
reciprocity (a).

**The derived Poincaré pairing is a morphism of Weil objects.** Let `φ` be a Weil datum on `K`,
`τ` one on `Λ_X(d)` for which the smooth trace `Ra_!(Λ_X(d)[2d]) ⟶ Λ_Y` is a morphism of Weil
objects (the trace square of `proposition-purity-trace-commute-frobenius`, the target
carrying the canonical datum), and `ψ` the contragredient datum on `K^∨(d)`, characterised by
the Frobenius equivariance of the twisted evaluation `K ⊗ᴸ K^∨(d) ⟶ Λ_X(d)`. Then

`β_K : Ra_! K ⊗ᴸ (Ra_* K^∨(d))[2d] ⟶ Λ_Y`

is a morphism of Weil objects, for the data `φ_{c,K}`, `φ_{K^∨(d)}[2d]` and the canonical datum
of `Λ_Y`. -/
theorem isWeilPairing_poincarePairing (sq : IsPullback g a a h) (γ : TateOrientation Λ a d)
    {K : DerivedCategoryModule Λ X} (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (τ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ X d) ⟶ tateObject Λ X d)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K) ⟶ twistedDual Λ d K)
    (hψ : IsWeilPairing g φ ψ τ (twistedEvaluation (tateObject Λ X d) K))
    (hTr : IsWeilMorphism h (lowerShriekWeilDatum sq (shiftWeilDatum g τ (2 * d)))
      (leftDerivedUpperStarUnitIso _ h).hom γ.smoothTrace) :
    IsWeilPairing h (lowerShriekWeilDatum sq φ)
      (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) (2 * d))
      (leftDerivedUpperStarUnitIso _ h).hom (γ.poincarePairing K) :=
  Etale.isWeilPairing_poincarePairing sq γ.dualizingComplexIso φ τ ψ hψ hTr

omit [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] in
/-- Blueprint `theorem-poincare-duality-frobenius`: Frobenius: equivariance, similitudine,
reciprocity (a).

**Frobenius equivariance of the degreewise pairing**, in the form
`⟨F_{c,K} x, F_{K^∨(d)} y⟩_i = F(⟨x, y⟩_i)` with `F` the Frobenius of the canonical datum on
`Λ = End(Λ_Y)` (see
`AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing_frobeniusOperator_eq` for the
form `⟨F_{c,K} x, F_{K^∨(d)} y⟩_i = ⟨x, y⟩_i`). The hypotheses are those of
`AlgebraicGeometry.Etale.TateOrientation.isWeilPairing_poincarePairing`; no nondegeneracy is
used. -/
theorem degreewisePoincarePairing_frobeniusOperator (sq : IsPullback g a a h)
    (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (τ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ X d) ⟶ tateObject Λ X d)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K) ⟶ twistedDual Λ d K)
    (hψ : IsWeilPairing g φ ψ τ (twistedEvaluation (tateObject Λ X d) K))
    (hTr : IsWeilMorphism h (lowerShriekWeilDatum sq (shiftWeilDatum g τ (2 * d)))
      (leftDerivedUpperStarUnitIso _ h).hom γ.smoothTrace)
    (i j : ℤ) (hij : i + j = 2 * d)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)
    (y : 𝟙_ (DerivedCategoryModule Λ Y) ⟶
      ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦j⟧) :
    γ.degreewisePoincarePairing K i j hij
        (frobeniusOperator h (shiftWeilDatum h (lowerShriekWeilDatum sq φ) i) x)
        (frobeniusOperator h (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) j) y) =
      frobeniusOperator h (leftDerivedUpperStarUnitIso _ h).hom
        (γ.degreewisePoincarePairing K i j hij x y) := by
  rw [degreewisePoincarePairing_apply, degreewisePoincarePairing_apply,
    ← frobeniusOperator_shiftWeilDatum_comp_shiftFunctorAdd',
    (isWeilPairing_poincarePairing sq γ φ τ ψ hψ hTr).degreewisePairing_frobeniusOperator,
    frobeniusOperator_shiftWeilDatum_comp_shiftFunctorZero']

omit [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] in
/-- Blueprint `theorem-poincare-duality-frobenius--3`: Equivariance of the twisted
pairing. This is also blueprint `theorem-poincare-duality-frobenius`: Frobenius: equivariance,
similitudine, reciprocity (a).

**Frobenius invariance of the degreewise pairing**: `⟨F_{c,K} x, F_{K^∨(d)} y⟩_i = ⟨x, y⟩_i`,
when every endomorphism of `Λ_Y` is a scalar (as for `Y = Spec k`, `k` separably closed), so
that geometric Frobenius acts trivially on the value ring `Λ`. As in the blueprint proof, `β_K`
is a morphism of Weil objects
(`AlgebraicGeometry.Etale.TateOrientation.isWeilPairing_poincarePairing`, Steps 1 and 2), whose
degree-zero part gives `⟨F_{c,K} x, F_{K^∨(d)} y⟩_i = F(⟨x, y⟩_i)`
(`AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing_frobeniusOperator`, Step 3),
and `F` acts trivially on the canonical datum of `Λ`. -/
theorem degreewisePoincarePairing_frobeniusOperator_eq (sq : IsPullback g a a h)
    (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (τ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ X d) ⟶ tateObject Λ X d)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K) ⟶ twistedDual Λ d K)
    (hψ : IsWeilPairing g φ ψ τ (twistedEvaluation (tateObject Λ X d) K))
    (hTr : IsWeilMorphism h (lowerShriekWeilDatum sq (shiftWeilDatum g τ (2 * d)))
      (leftDerivedUpperStarUnitIso _ h).hom γ.smoothTrace)
    (hY : ∀ v : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ 𝟙_ _, ∃ c : Λ, v = c • 𝟙 _)
    (i j : ℤ) (hij : i + j = 2 * d)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)
    (y : 𝟙_ (DerivedCategoryModule Λ Y) ⟶
      ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦j⟧) :
    γ.degreewisePoincarePairing K i j hij
        (frobeniusOperator h (shiftWeilDatum h (lowerShriekWeilDatum sq φ) i) x)
        (frobeniusOperator h (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) j) y) =
      γ.degreewisePoincarePairing K i j hij x y := by
  rw [degreewisePoincarePairing_frobeniusOperator sq γ φ τ ψ hψ hTr,
    frobeniusOperator_unit_eq_self h hY]

/-- Blueprint `theorem-poincare-duality-frobenius`: Frobenius: equivariance, similitudine,
reciprocity (a).

**The untwisted derived Poincaré pairing is a morphism of Weil objects.** Let `φ` be a Weil
datum on `K`, `ψ` the contragredient datum on `K^∨`, characterised by the Frobenius equivariance
of the evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X` (the target carrying the canonical datum), and `τ` a Weil
datum on `Λ_Y(-d)` for which the untwisted smooth trace `(Ra_! Λ_X)[2d] ⟶ Λ_Y(-d)` is a
morphism of Weil objects. Then `β_K^{untw} : Ra_! K ⊗ᴸ (Ra_* K^∨)[2d] ⟶ Λ_Y(-d)` is a morphism
of Weil objects for the data `φ_{c,K}`, `φ_{K^∨}[2d]` and `τ`. -/
theorem isWeilPairing_untwistedPoincarePairing (sq : IsPullback g a a h)
    (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj ((DerivedCategory.coefficientDual _ X).obj (op K)) ⟶
      (DerivedCategory.coefficientDual _ X).obj (op K))
    (hψ : IsWeilPairing g φ ψ (leftDerivedUpperStarUnitIso _ g).hom
      (DerivedCategory.coefficientEvaluation K))
    (τ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ Y (-d)) ⟶ tateObject Λ Y (-d))
    (hTr : IsWeilMorphism h
      (shiftWeilDatum h (lowerShriekWeilDatum sq (leftDerivedUpperStarUnitIso _ g).hom) (2 * d))
      τ γ.untwistedSmoothTrace) :
    IsWeilPairing h (lowerShriekWeilDatum sq φ)
      (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) (2 * d)) τ
      (γ.untwistedPoincarePairing K) :=
  isWeilPairing_poincarePairingOfTrace sq φ ψ hψ (2 * d) _ τ hTr

/-- Blueprint `theorem-poincare-duality-frobenius--4`: Untwisted similitude.

**The untwisted similitude.** With the hypotheses of
`AlgebraicGeometry.Etale.TateOrientation.isWeilPairing_untwistedPoincarePairing`, and if
geometric Frobenius acts on the value line `Λ(-d) = Hom(Λ_Y, Λ_Y(-d))` by `q^d` (the
normalisation `prose-10-21` of the datum `τ`), then for
`x ∈ H^i_c(X, K)` and `y ∈ H^{2d-i}(X, K^∨)`

`⟨F_{c,K} x, F_{K^∨} y⟩^{untw}_i = q^d ⟨x, y⟩^{untw}_i`.

These are identities of bilinear maps; no nondegeneracy is used. -/
theorem untwistedDegreewisePoincarePairing_frobeniusOperator (sq : IsPullback g a a h)
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
    (q : ℕ) (hτ : ∀ z, frobeniusOperator h τ z = ((q : Λ) ^ d) • z)
    (i j : ℤ) (hij : i + j = 2 * d)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)
    (y : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
      ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦j⟧) :
    γ.untwistedDegreewisePoincarePairing K i j hij
        (frobeniusOperator h (shiftWeilDatum h (lowerShriekWeilDatum sq φ) i) x)
        (frobeniusOperator h (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq ψ) j) y) =
      ((q : Λ) ^ d) • γ.untwistedDegreewisePoincarePairing K i j hij x y := by
  rw [untwistedDegreewisePoincarePairing_apply, untwistedDegreewisePoincarePairing_apply,
    ← frobeniusOperator_shiftWeilDatum_comp_shiftFunctorAdd',
    (isWeilPairing_untwistedPoincarePairing sq γ φ ψ hψ τ hTr).degreewisePairing_frobeniusOperator,
    frobeniusOperator_shiftWeilDatum_comp_shiftFunctorZero', hτ]

/-- Blueprint `theorem-poincare-duality-frobenius--4`: Untwisted similitude.

**The untwisted similitude for the constant complex.** Let `K = Λ_X` with its canonical datum,
`ψ` the contragredient datum on `Λ_X^∨`, and `ι : Λ_X ⟶ Λ_X^∨` a morphism of Weil objects from
the canonical datum to `ψ` (the canonical identification `Λ_X^∨ ≅ Λ_X`). Then for
`x ∈ H^i_c(X, Λ)` and `y ∈ H^{2d-i}(X, Λ)`, with `F` the geometric Frobenius of the canonical
datum on both, the pairing `⟨x, y⟩ = ⟨x, ι_* y⟩^{untw}_i` satisfies
`⟨F x, F y⟩ = q^d ⟨x, y⟩`. -/
theorem untwistedDegreewisePoincarePairing_unit_frobeniusOperator (sq : IsPullback g a a h)
    (γ : TateOrientation Λ a d)
    (ψ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.coefficientDual _ X).obj (op (𝟙_ (DerivedCategoryModule Λ X)))) ⟶
      (DerivedCategory.coefficientDual _ X).obj (op (𝟙_ (DerivedCategoryModule Λ X))))
    (hψ : IsWeilPairing g (leftDerivedUpperStarUnitIso _ g).hom ψ
      (leftDerivedUpperStarUnitIso _ g).hom (DerivedCategory.coefficientEvaluation _))
    (ι : 𝟙_ (DerivedCategoryModule Λ X) ⟶
      (DerivedCategory.coefficientDual _ X).obj (op (𝟙_ (DerivedCategoryModule Λ X))))
    (hι : IsWeilMorphism g (leftDerivedUpperStarUnitIso _ g).hom ψ ι)
    (τ : (L((h)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ Y (-d)) ⟶ tateObject Λ Y (-d))
    (hTr : IsWeilMorphism h
      (shiftWeilDatum h (lowerShriekWeilDatum sq (leftDerivedUpperStarUnitIso _ g).hom) (2 * d))
      τ γ.untwistedSmoothTrace)
    (q : ℕ) (hτ : ∀ z, frobeniusOperator h τ z = ((q : Λ) ^ d) • z)
    (i j : ℤ) (hij : i + j = 2 * d)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶
      ((R(a)_![ModuleCat.{u + 1} Λ]).obj (𝟙_ (DerivedCategoryModule Λ X)))⟦i⟧)
    (y : 𝟙_ (DerivedCategoryModule Λ Y) ⟶
      ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (𝟙_ (DerivedCategoryModule Λ X)))⟦j⟧) :
    γ.untwistedDegreewisePoincarePairing _ i j hij
        (frobeniusOperator h (shiftWeilDatum h
          (lowerShriekWeilDatum sq (leftDerivedUpperStarUnitIso _ g).hom) i) x)
        (frobeniusOperator h (shiftWeilDatum h
            (lowerStarWeilDatum sq.toCommSq (leftDerivedUpperStarUnitIso _ g).hom) j) y ≫
          ((R((a)_*[ModuleCat.{u + 1} Λ])).map ι)⟦j⟧') =
      ((q : Λ) ^ d) • γ.untwistedDegreewisePoincarePairing _ i j hij x
        (y ≫ ((R((a)_*[ModuleCat.{u + 1} Λ])).map ι)⟦j⟧') := by
  rw [← ((hι.rightDerivedLowerStar_map sq.toCommSq).shift j).frobeniusOperator_comp,
    untwistedDegreewisePoincarePairing_frobeniusOperator sq γ _ ψ hψ τ hTr q hτ]

end Equivariance

end TateOrientation

end Etale

end AlgebraicGeometry
