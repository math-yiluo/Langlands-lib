/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.EtaleCohomology.PoincareDuality.Frobenius.Equivariance
public import WeilConjectures.SixFunctors.Etale.Derived.WeilDual

/-!
# Frobenius: the dual and Tate data

Blueprint `theorem-poincare-duality-frobenius--2`, in the language of Weil data
(`AlgebraicGeometry.Etale.IsWeilMorphism`, `AlgebraicGeometry.Etale.IsWeilPairing`) at a finite
coefficient ring `Λ`. Let `φ : Lg^* K ≅ K` be a Weil datum on `K ∈ D(X_ét, Λ)` and
`φ_{K^∨}` the contragredient datum on `K^∨ = RHom(K, Λ_X)`
(`AlgebraicGeometry.Etale.contragredientWeilDatum`, `theorem-poincare-duality-frobenius--1`). Then:

* `φ_{K^∨}` is an isomorphism for a perfect `K`
  (`AlgebraicGeometry.Etale.isIso_contragredientWeilDatum`), and `K^∨` is again perfect
  (`AlgebraicGeometry.Etale.DerivedCategory.isDualizable_coefficientDual`);
* the evaluation `K ⊗ᴸ K^∨ ⟶ Λ_X` is a morphism of Weil objects
  (`AlgebraicGeometry.Etale.isWeilPairing_coefficientEvaluation`);
* for a datum `τ` on `T` (the Tate datum `τ_r` on `Λ_X(r)`), the twisted dual `K^∨ ⊗ᴸ T` with the
  datum `φ_{K^∨} ⊗ τ` is a Weil object
  (`AlgebraicGeometry.Etale.isIso_tensorWeilDatum`) and the twisted evaluation
  `K ⊗ᴸ (K^∨ ⊗ᴸ T) ⟶ T` is a morphism of Weil objects
  (`AlgebraicGeometry.Etale.isWeilPairing_twistedEvaluation`).

This discharges the equivariance hypothesis on the dual datum in the Frobenius equivariance of
the Poincaré pairing (`theorem-poincare-duality-frobenius--3`,
`AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing_frobeniusOperator_eq_of_iso`).

## Implementation notes

The blueprint also asserts that the identification `𝔻_X K ≅ K^∨(d)[2d]` is an isomorphism of
Weil objects. It rests on the Weil equivariance of purity and of the trace
(`proposition-purity-trace-commute-frobenius`), which is not formalised: the Frobenius files
take the equivariance of the smooth trace as a hypothesis, and no Weil datum on `𝔻_X K` is
defined. That clause is therefore omitted, and so is the transport clause (finite reduction,
adic normalization, rationalization, coefficient extension, idempotent splitting): Weil data are
only formalised at a finite coefficient ring, where none of these functors act on them.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Data

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}} (g : X ⟶ X)
  {K : DerivedCategoryModule Λ X}

/-- The tensor product `ψ_A ⊗ ψ_B` of two Weil data which are isomorphisms is an
isomorphism. -/
instance isIso_tensorWeilDatum {A B : DerivedCategoryModule Λ X}
    (ψA : (L((g)^*[ModuleCat.{u + 1} Λ])).obj A ⟶ A)
    (ψB : (L((g)^*[ModuleCat.{u + 1} Λ])).obj B ⟶ B) [IsIso ψA] [IsIso ψB] :
    IsIso (tensorWeilDatum g ψA ψB) := by
  unfold tensorWeilDatum
  infer_instance

/-- Blueprint `theorem-poincare-duality-frobenius--2`: Compatibility of the dual and Tate data.

**The evaluation is a morphism of Weil objects**: for a Weil datum `φ : Lg^* K ≅ K`, the
coefficient evaluation `ev_K : K ⊗ᴸ K^∨ ⟶ Λ_X` is a Weil pairing for `φ`, the contragredient
datum `φ_{K^∨}` (`AlgebraicGeometry.Etale.contragredientWeilDatum`) and the canonical datum of
`Λ_X`. -/
theorem isWeilPairing_coefficientEvaluation (φ : L((g)^*[ModuleCat.{u + 1} Λ]).obj K ≅ K) :
    IsWeilPairing g φ.hom (contragredientWeilDatum _ g φ) (leftDerivedUpperStarUnitIso _ g).hom
      (DerivedCategory.coefficientEvaluation K) :=
  map_coefficientEvaluation_comp_leftDerivedUpperStarUnitIso_hom _ g φ

/-- Blueprint `theorem-poincare-duality-frobenius--2`: Compatibility of the dual and Tate data.

**The twisted dual is a Weil object**: for a Weil datum `φ : Lg^* K ≅ K` on a perfect `K` and
a Weil datum `τ : Lg^* T ≅ T` (for `T = Λ_X(r)`, the Tate datum `τ_r`), the datum
`φ_{K^∨} ⊗ τ` on `K^∨ ⊗ᴸ T` is an isomorphism. -/
theorem isIso_tensorWeilDatum_contragredientWeilDatum
    (φ : L((g)^*[ModuleCat.{u + 1} Λ]).obj K ≅ K) (hK : IsDualizable K)
    {T : DerivedCategoryModule Λ X} (τ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj T ⟶ T)
    [IsIso τ] : IsIso (tensorWeilDatum g (contragredientWeilDatum _ g φ) τ) := by
  have := isIso_contragredientWeilDatum _ g φ hK
  infer_instance

/-- Blueprint `theorem-poincare-duality-frobenius--2`: Compatibility of the dual and Tate data.

**The twisted evaluation is a morphism of Weil objects**: for a Weil datum `φ : Lg^* K ≅ K` and
a Weil datum `τ` on `T` (for `T = Λ_X(r)`, the Tate datum `τ_r`), the twisted evaluation
`K ⊗ᴸ (K^∨ ⊗ᴸ T) ⟶ T` (`AlgebraicGeometry.Etale.twistedEvaluation`) is a Weil pairing for `φ`,
the twisted datum `φ_{K^∨(r)} = φ_{K^∨} ⊗ τ` and `τ`. -/
theorem isWeilPairing_twistedEvaluation (φ : L((g)^*[ModuleCat.{u + 1} Λ]).obj K ≅ K)
    {T : DerivedCategoryModule Λ X} (τ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj T ⟶ T) :
    IsWeilPairing g φ.hom (tensorWeilDatum g (contragredientWeilDatum _ g φ) τ) τ
      (twistedEvaluation T K) :=
  map_twistedEvaluation_comp _ g φ τ

end Data

namespace TateOrientation

section Equivariance

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y} [HasCompactification a] [QuasiCompact a] {d : ℕ} {g : X ⟶ X} {h : Y ⟶ Y}

/-- Blueprint `theorem-poincare-duality-frobenius`: Frobenius: equivariance, similitudine,
reciprocity (a).

**The derived Poincaré pairing is a morphism of Weil objects**, for the contragredient twisted
datum: `AlgebraicGeometry.Etale.TateOrientation.isWeilPairing_poincarePairing` with the datum
`φ_{K^∨(d)} = φ_{K^∨} ⊗ τ` on `K^∨(d)`, whose equivariance hypothesis is discharged by
`theorem-poincare-duality-frobenius--2`
(`AlgebraicGeometry.Etale.isWeilPairing_twistedEvaluation`). -/
theorem isWeilPairing_poincarePairing_of_iso (sq : IsPullback g a a h)
    (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ≅ K)
    (τ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ X d) ⟶ tateObject Λ X d)
    (hTr : IsWeilMorphism h (lowerShriekWeilDatum sq (shiftWeilDatum g τ (2 * d)))
      (leftDerivedUpperStarUnitIso _ h).hom γ.smoothTrace) :
    IsWeilPairing h (lowerShriekWeilDatum sq φ.hom)
      (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq
        (tensorWeilDatum g (contragredientWeilDatum _ g φ) τ)) (2 * d))
      (leftDerivedUpperStarUnitIso _ h).hom (γ.poincarePairing K) :=
  isWeilPairing_poincarePairing sq γ φ.hom τ _ (isWeilPairing_twistedEvaluation g φ τ) hTr

/-- Blueprint `theorem-poincare-duality-frobenius--3`: Equivariance of the twisted
pairing.

**Frobenius invariance of the degreewise pairing** `⟨F_{c,K} x, F_{K^∨(d)} y⟩_i = ⟨x, y⟩_i`, for
a Weil datum `φ : Lg^* K ≅ K`, the Frobenius `F_{K^∨(d)}` being that of the twisted
contragredient datum `φ_{K^∨(d)} = φ_{K^∨} ⊗ τ` of `theorem-poincare-duality-frobenius--1`: this is
`AlgebraicGeometry.Etale.TateOrientation.degreewisePoincarePairing_frobeniusOperator_eq` with the
equivariance of the twisted evaluation supplied by `theorem-poincare-duality-frobenius--2`
(`AlgebraicGeometry.Etale.isWeilPairing_twistedEvaluation`). The equivariance `hTr` of the
smooth trace (`proposition-purity-trace-commute-frobenius`) remains a hypothesis. -/
theorem degreewisePoincarePairing_frobeniusOperator_eq_of_iso (sq : IsPullback g a a h)
    (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ≅ K)
    (τ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ X d) ⟶ tateObject Λ X d)
    (hTr : IsWeilMorphism h (lowerShriekWeilDatum sq (shiftWeilDatum g τ (2 * d)))
      (leftDerivedUpperStarUnitIso _ h).hom γ.smoothTrace)
    (hY : ∀ v : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ 𝟙_ _, ∃ c : Λ, v = c • 𝟙 _)
    (i j : ℤ) (hij : i + j = 2 * d)
    (x : 𝟙_ (DerivedCategoryModule Λ Y) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)
    (y : 𝟙_ (DerivedCategoryModule Λ Y) ⟶
      ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦j⟧) :
    γ.degreewisePoincarePairing K i j hij
        (frobeniusOperator h (shiftWeilDatum h (lowerShriekWeilDatum sq φ.hom) i) x)
        (frobeniusOperator h (shiftWeilDatum h (lowerStarWeilDatum sq.toCommSq
          (tensorWeilDatum g (contragredientWeilDatum _ g φ) τ)) j) y) =
      γ.degreewisePoincarePairing K i j hij x y :=
  degreewisePoincarePairing_frobeniusOperator_eq sq γ φ.hom τ _
    (isWeilPairing_twistedEvaluation g φ τ) hTr hY i j hij x y

/-- Blueprint `theorem-poincare-duality-frobenius--4`: Untwisted similitude.

**The untwisted similitude** `⟨F_{c,K} x, F_{K^∨} y⟩^{untw}_i = q^d ⟨x, y⟩^{untw}_i`, for a
Weil datum `φ : Lg^* K ≅ K`, the Frobenius `F_{K^∨}` being that of the contragredient datum of
`theorem-poincare-duality-frobenius--1`, whose equivariance is supplied by
`theorem-poincare-duality-frobenius--2`
(`AlgebraicGeometry.Etale.isWeilPairing_coefficientEvaluation`). -/
theorem untwistedDegreewisePoincarePairing_frobeniusOperator_of_iso [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] (sq : IsPullback g a a h)
    (γ : TateOrientation Λ a d) {K : DerivedCategoryModule Λ X}
    (φ : (L((g)^*[ModuleCat.{u + 1} Λ])).obj K ≅ K)
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
        (frobeniusOperator h (shiftWeilDatum h (lowerShriekWeilDatum sq φ.hom) i) x)
        (frobeniusOperator h (shiftWeilDatum h
          (lowerStarWeilDatum sq.toCommSq (contragredientWeilDatum _ g φ)) j) y) =
      ((q : Λ) ^ d) • γ.untwistedDegreewisePoincarePairing K i j hij x y :=
  untwistedDegreewisePoincarePairing_frobeniusOperator sq γ φ.hom _
    (isWeilPairing_coefficientEvaluation g φ) τ hTr q hτ i j hij x y

end Equivariance

end TateOrientation

end Etale

end AlgebraicGeometry
