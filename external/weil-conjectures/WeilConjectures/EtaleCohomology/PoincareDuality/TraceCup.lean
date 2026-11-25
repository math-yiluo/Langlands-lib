/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Monoidal.ShiftUnitor
public import WeilConjectures.EtaleCohomology.PoincareDuality.Pairing
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar

/-!
# The trace map and the trace–cup pairing

Let `a : X ⟶ Y` be a morphism admitting a compactification, `Λ` a coefficient ring with a Tate
twist datum and `γ : Λ_X(d)[2d] ≅ Ra^! Λ_Y` a Tate orientation of `a`. Over `Y = Spec k` this
is the setting of the Poincaré duality chapter, and this file defines its trace map and its
trace–cup pairing.

Cohomology classes are morphisms out of the unit: a class of degree `n` of `X` with
coefficients `Λ` is a morphism `Λ_X ⟶ Λ_X[n]` in `D(X_ét, Λ)`, so that
`H^n(X, Λ) = Hom(Λ_X, Λ_X[n])`, and a compactly supported class is a morphism
`Λ_Y ⟶ (Ra_! Λ_X)[n]` in `D(Y_ét, Λ)`, so that `H^n_c(X, Λ) = Hom(Λ_Y, (Ra_! Λ_X)[n])` when
`Y = Spec k` with `k` separably closed. The value group `Λ(-d)` of the untwisted trace is
`Hom(Λ_Y, Λ_Y(-d))`.

* The *trace map* `tr_X : H^{2d}_c(X, Λ(d)) ⟶ Λ` composes a class with the smooth trace
  `Ra_!(Λ_X(d)[2d]) ⟶ Λ_Y`, which is the counit of `Ra_! ⊣ Ra^!` read through `γ`.
* Its *untwisted form* `tr^{(-d)}_X : H^{2d}_c(X, Λ) ⟶ Λ(-d)` composes a class with the
  untwisted smooth trace `(Ra_! Λ_X)[2d] ⟶ Λ_Y(-d)`: the smooth trace tensored with `Λ_Y(-d)`,
  through the projection map `Ra_! Λ_X ⊗ Λ_Y(d) ⟶ Ra_!(Λ_X ⊗ La^* Λ_Y(d))` and
  `Λ_Y(d) ⊗ Λ_Y(-d) ≅ Λ_Y`. Neither uses properness.
* For `a` proper, `Ra_! ≅ Ra_*` identifies `H^n(X, Λ)` with `H^n_c(X, Λ)`.
* The *cup product* `H^i(X, Λ) × H^j(X, Λ) ⟶ H^{i+j}(X, Λ)` is induced by the multiplication
  `Λ_X ⊗ Λ_X ≅ Λ_X`.
* For `a` proper and `i + j = 2d`, the *trace–cup pairing* is
  `⟨x, y⟩ = tr^{(-d)}_X(x ⌣ y) : H^i(X, Λ) × H^j(X, Λ) ⟶ Λ(-d)`.

## Main definitions

- `AlgebraicGeometry.Etale.cupProduct` (`corollary-cup-product-pairing--1`): the cup product.
- `AlgebraicGeometry.Etale.cohomologyAddEquivCompactSupport`
(`theorem-trace-isomorphism-top-degree`):
  `H^n(X, Λ) ≃ H^n_c(X, Λ)` for a proper morphism.
- `AlgebraicGeometry.Etale.TateOrientation.traceMap` (`corollary-cup-product-pairing--1`,
  `theorem-trace-isomorphism-top-degree`): `tr_X : H^{2d}_c(X, Λ(d)) ⟶ Λ`.
- `AlgebraicGeometry.Etale.TateOrientation.untwistedSmoothTrace`,
  `AlgebraicGeometry.Etale.TateOrientation.untwistedTraceMap` (`corollary-cup-product-pairing--1`,
  `theorem-trace-isomorphism-top-degree`): `tr^{(-d)}_X : H^{2d}_c(X, Λ) ⟶ Λ(-d)`.
- `AlgebraicGeometry.Etale.TateOrientation.traceCupPairing` (`corollary-cup-product-pairing--1`,
  `corollary-cup-product-pairing--1`): `⟨x, y⟩ = tr^{(-d)}_X(x ⌣ y)`.

## Main statements

- `AlgebraicGeometry.Etale.cupProduct_comm` (`corollary-cup-product-pairing--1`): the cup product is
  graded commutative, `y ⌣ x = (-1)^{ij} x ⌣ y`.

## Implementation notes

The Hom groups of `D(Y_ét, Λ)` are not given a `Λ`-module structure in the repository, so the
trace maps, the cup product and the pairing are additive (biadditive), not `Λ`-(bi)linear.

The complementary degrees of the pairing are two indices `i j : ℤ` with `i + j = 2 * d`, since
`2 * d - (2 * d - i)` is not definitionally `i`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A]

/-- The derived category `D(X_ét, A)` of `A`-valued étale sheaves on `X`. -/
local notation "𝐃(" X ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology X) A)

variable {X Y : Scheme.{u}}

/-- The cup product of two cohomology classes `x : Λ_X ⟶ Λ_X[i]` and `y : Λ_X ⟶ Λ_X[j]`,
induced by the multiplication `λ : Λ_X ⊗ᴸ Λ_X ≅ Λ_X`,
```
       λ⁻¹                  x ⊗ y                         ≅                       λ[i + j]
Λ_X ──────▶ Λ_X ⊗ᴸ Λ_X ─────────▶ Λ_X[i] ⊗ᴸ Λ_X[j] ─────▶ (Λ_X ⊗ᴸ Λ_X)[i + j] ──────────▶ Λ_X[i + j]
```
where the middle isomorphism moves the shifts out of the tensor product
(`AlgebraicGeometry.Etale.derivedTensorShiftIso`). -/
noncomputable def cupProductAux {i j : ℤ} (x : (𝟙_ 𝐃(X, A)) ⟶ (𝟙_ 𝐃(X, A))⟦i⟧)
    (y : (𝟙_ 𝐃(X, A)) ⟶ (𝟙_ 𝐃(X, A))⟦j⟧) : (𝟙_ 𝐃(X, A)) ⟶ (𝟙_ 𝐃(X, A))⟦i + j⟧ :=
  (derivedTensorLeftUnitor A X (𝟙_ _)).inv ≫ ((derivedTensor A X).map x).app _ ≫
    ((derivedTensor A X).obj _).map y ≫ (derivedTensorShiftIso A (𝟙_ _) (𝟙_ _) i j).hom ≫
      (derivedTensorLeftUnitor A X (𝟙_ _)).hom⟦i + j⟧'

lemma cupProductAux_add_left {i j : ℤ} (x x' : (𝟙_ 𝐃(X, A)) ⟶ (𝟙_ 𝐃(X, A))⟦i⟧)
    (y : (𝟙_ 𝐃(X, A)) ⟶ (𝟙_ 𝐃(X, A))⟦j⟧) :
    cupProductAux A (x + x') y = cupProductAux A x y + cupProductAux A x' y := by
  simp [cupProductAux, derivedTensor]

lemma cupProductAux_add_right {i j : ℤ} (x : (𝟙_ 𝐃(X, A)) ⟶ (𝟙_ 𝐃(X, A))⟦i⟧)
    (y y' : (𝟙_ 𝐃(X, A)) ⟶ (𝟙_ 𝐃(X, A))⟦j⟧) :
    cupProductAux A x (y + y') = cupProductAux A x y + cupProductAux A x y' := by
  simp [cupProductAux, derivedTensor, MonoidalPreadditive.whiskerLeft_add]

/-- Blueprint `corollary-cup-product-pairing--1`: Poincare trace and cup-product pairing.

The *cup product* `⌣ : H^i(X, Λ) × H^j(X, Λ) ⟶ H^{i+j}(X, Λ)` on the cohomology classes
`Λ_X ⟶ Λ_X[n]` of `D(X_ét)`, induced by the multiplication `Λ_X ⊗ᴸ Λ_X ≅ Λ_X`
(`AlgebraicGeometry.Etale.cupProductAux`), as a biadditive map. -/
noncomputable def cupProduct (i j : ℤ) :
    ((𝟙_ 𝐃(X, A)) ⟶ (𝟙_ 𝐃(X, A))⟦i⟧) →+ ((𝟙_ 𝐃(X, A)) ⟶ (𝟙_ 𝐃(X, A))⟦j⟧) →+
      ((𝟙_ 𝐃(X, A)) ⟶ (𝟙_ 𝐃(X, A))⟦i + j⟧) :=
  AddMonoidHom.mk' (fun x ↦ AddMonoidHom.mk' (cupProductAux A x)
    (cupProductAux_add_right A x)) fun x x' ↦ by
      ext y
      exact cupProductAux_add_left A x x' y

lemma cupProduct_apply {i j : ℤ} (x : (𝟙_ 𝐃(X, A)) ⟶ (𝟙_ 𝐃(X, A))⟦i⟧)
    (y : (𝟙_ 𝐃(X, A)) ⟶ (𝟙_ 𝐃(X, A))⟦j⟧) :
    cupProduct A i j x y = cupProductAux A x y :=
  rfl

/-- The cup product is the product of classes of the unit of the monoidal category `D(X_ét)`
(`CategoryTheory.MonoidalCategory.shiftProduct`). -/
lemma cupProduct_eq_shiftProduct {i j : ℤ} (x : (𝟙_ 𝐃(X, A)) ⟶ (𝟙_ 𝐃(X, A))⟦i⟧)
    (y : (𝟙_ 𝐃(X, A)) ⟶ (𝟙_ 𝐃(X, A))⟦j⟧) :
    cupProduct A i j x y = MonoidalCategory.shiftProduct x y := by
  rw [cupProduct_apply, cupProductAux, MonoidalCategory.shiftProduct, derivedTensorShiftIso]
  simp only [Iso.trans_hom, Iso.app_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rfl

/-- Blueprint `corollary-cup-product-pairing--1`: Poincare trace and cup-product pairing.

**The cup product is graded commutative**: for `x ∈ H^i(X, Λ)` and `y ∈ H^j(X, Λ)`,
`y ⌣ x = (-1)^{ij} x ⌣ y`, the two sides being compared along `Λ_X[j + i] = Λ_X[i + j]`.

This is the Eckmann–Hilton argument: `x ⊗ y = (x ⊗ 1) ≫ (1 ⊗ y) = (1 ⊗ y) ≫ (x ⊗ 1)`, and
the two ways of moving the shifts out of `Λ_X[i] ⊗ᴸ Λ_X[j]` differ by `(-1)^{ij}`
(`CategoryTheory.MonoidalCategory.shiftProduct_comm`). -/
theorem cupProduct_comm {i j : ℤ} (x : (𝟙_ 𝐃(X, A)) ⟶ (𝟙_ 𝐃(X, A))⟦i⟧)
    (y : (𝟙_ 𝐃(X, A)) ⟶ (𝟙_ 𝐃(X, A))⟦j⟧) :
    cupProduct A j i y x =
      (i * j).negOnePow • (cupProduct A i j x y ≫ eqToHom (by rw [add_comm])) := by
  rw [cupProduct_eq_shiftProduct, cupProduct_eq_shiftProduct]
  exact MonoidalCategory.shiftProduct_comm (DerivedCategory.unitorsCommShift _) x y

variable {A}

/-- The identification `Ra_*(Λ_X[n]) ≅ (Ra_! Λ_X)[n]` for a proper morphism `a`: the shift
compatibility of `Ra_*` followed by `Ra_* ≅ Ra_!`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekIsoRightDerivedLowerStar`). -/
noncomputable def rightDerivedLowerStarShiftIsoLowerShriek (a : X ⟶ Y) [HasCompactification a]
    [IsProper a] (M : 𝐃(X, A)) (n : ℤ) :
    (R((a)_*[A])).obj (M⟦n⟧) ≅ ((R(a)_![A]).obj M)⟦n⟧ :=
  ((R((a)_*[A])).commShiftIso n).app M ≪≫
    (shiftFunctor _ n).mapIso ((rightDerivedLowerShriekIsoRightDerivedLowerStar A a).app M).symm

/-- Blueprint `theorem-trace-isomorphism-top-degree`: Poincare duality conventions: trace and
trace-cup pairing.

For a proper morphism `a : X ⟶ Y`, ordinary and compactly supported cohomology agree:
`H^n(X, Λ) = Hom(Λ_X, Λ_X[n]) ≃ Hom(Λ_Y, (Ra_! Λ_X)[n]) = H^n_c(X, Λ)`. The equivalence is
the adjunction `La^* ⊣ Ra_*` read through an identification `e : La^* Λ_Y ≅ Λ_X`, followed by
`Ra_*(Λ_X[n]) ≅ (Ra_! Λ_X)[n]` (`Ra_! ≅ Ra_*` for `a` proper),
```
 x ↦ ( Λ_Y ──unit──▶ Ra_* La^* Λ_Y ──Ra_*(e ≫ x)──▶ Ra_*(Λ_X[n]) ≅ (Ra_! Λ_X)[n] ).
``` -/
noncomputable def cohomologyAddEquivCompactSupport (a : X ⟶ Y) [HasCompactification a]
    [IsProper a] (e : (L((a)^*[A])).obj (𝟙_ _) ≅ 𝟙_ _) (n : ℤ) :
    ((𝟙_ 𝐃(X, A)) ⟶ (𝟙_ 𝐃(X, A))⟦n⟧) ≃+ ((𝟙_ 𝐃(Y, A)) ⟶ ((R(a)_![A]).obj (𝟙_ _))⟦n⟧) where
  toFun x := (derivedUpperStarLowerStarAdjunction A a).homEquiv _ _ (e.hom ≫ x) ≫
    (rightDerivedLowerStarShiftIsoLowerShriek a (𝟙_ _) n).hom
  invFun z := e.inv ≫ ((derivedUpperStarLowerStarAdjunction A a).homEquiv _ _).symm
    (z ≫ (rightDerivedLowerStarShiftIsoLowerShriek a (𝟙_ _) n).inv)
  left_inv x := by simp
  right_inv z := by simp
  map_add' x x' := by
    simp [Adjunction.homEquiv_unit, Preadditive.comp_add, Preadditive.add_comp]

end General

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}

namespace TateOrientation

variable {a : X ⟶ Y} [HasCompactification a] {d : ℕ}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

/-- Blueprint `corollary-cup-product-pairing--1`: Poincare trace and cup-product pairing.

The *trace map* `tr_X : H^{2d}_c(X, Λ(d)) ⟶ Λ` of a Tate orientation `γ`: a compactly
supported class `Λ_Y ⟶ (Ra_! Λ_X(d))[2d]` is composed with the shift compatibility of `Ra_!`
and the smooth trace `Ra_!(Λ_X(d)[2d]) ⟶ Λ_Y`
(`AlgebraicGeometry.Etale.TateOrientation.smoothTrace`), the counit of `Ra_! ⊣ Ra^!` read
through `γ`. The target `Hom(Λ_Y, Λ_Y)` is `Λ` for `Y = Spec k`.

This is also the trace map of `theorem-trace-isomorphism-top-degree`: it does not use properness. -/
noncomputable def traceMap (γ : TateOrientation Λ a d) :
    ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶
        ((R(a)_![ModuleCat.{u + 1} Λ]).obj (tateObject Λ X d))⟦(2 * d : ℤ)⟧) →+
      ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ 𝟙_ (DerivedCategoryModule Λ Y)) :=
  Preadditive.rightComp _
    (((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).inv.app _ ≫ γ.smoothTrace)

/-- The *twisted smooth trace* `(Ra_! Λ_X)[2d] ⊗ᴸ Λ_Y(d) ⟶ Λ_Y` of a Tate orientation `γ`:
the projection map of `Ra_!` and `La^* Λ_Y(d) ≅ Λ_X(d)` turn the source into
`Ra_!(Λ_X(d)[2d])`, on which the smooth trace is evaluated,
```
                          ≅                              projection map
(Ra_! Λ_X)[2d] ⊗ᴸ Λ_Y(d) ───▶ (Ra_! Λ_X ⊗ᴸ Λ_Y(d))[2d] ────────────────▶
                                    ≅                                ≅                  Tr_γ
  (Ra_!(Λ_X ⊗ᴸ La^* Λ_Y(d)))[2d] ─────▶ (Ra_! Λ_X(d))[2d] ─────▶ Ra_!(Λ_X(d)[2d]) ──────▶ Λ_Y
``` -/
noncomputable def twistedSmoothTrace (γ : TateOrientation Λ a d) :
    ((derivedTensor _ Y).obj (((R(a)_![ModuleCat.{u + 1} Λ]).obj
        (constantComplex Λ X))⟦(2 * d : ℤ)⟧)).obj (tateObject Λ Y d) ⟶
      𝟙_ (DerivedCategoryModule Λ Y) :=
  (((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).commShiftIso (2 * d : ℤ)).hom.app _ ≫
    (((projectionMap _ a).app (constantComplex Λ X)).app (tateObject Λ Y d))⟦(2 * d : ℤ)⟧' ≫
      ((R(a)_![ModuleCat.{u + 1} Λ]).map (((derivedTensor _ X).obj _).map
        (leftDerivedUpperStarTateObjectIso a d).hom ≫
          (derivedTensorLeftUnitor _ X _).hom))⟦(2 * d : ℤ)⟧' ≫
        ((R(a)_![ModuleCat.{u + 1} Λ]).commShiftIso (2 * d : ℤ)).inv.app _ ≫ γ.smoothTrace

/-- The identification `Λ_Y ≅ Λ_Y(d) ⊗ᴸ Λ_Y(-d)` of the Tate twist datum. -/
noncomputable def constantComplexIsoTateObjectTensor (Y : Scheme.{u}) [HasInvertibleExponent Λ Y]
    (d : ℕ) :
    𝟙_ (DerivedCategoryModule Λ Y) ≅
      ((derivedTensor _ Y).obj (tateObject Λ Y d)).obj (tateObject Λ Y (-d)) :=
  (HasTateTwist.twistObjectZeroIso Y).symm ≪≫ eqToIso (by rw [add_neg_cancel]) ≪≫
    (HasTateTwist.twistObjectAddIso Y d (-d)).symm

/-- Blueprint `theorem-trace-isomorphism-top-degree`: Poincare duality conventions: trace and
trace-cup pairing.

The *untwisted smooth trace* `(Ra_! Λ_X)[2d] ⟶ Λ_Y(-d)` of a Tate orientation `γ`: the
twisted smooth trace `(Ra_! Λ_X)[2d] ⊗ᴸ Λ_Y(d) ⟶ Λ_Y`
(`AlgebraicGeometry.Etale.TateOrientation.twistedSmoothTrace`) tensored with `Λ_Y(-d)`, read
through `Λ_Y(d) ⊗ᴸ Λ_Y(-d) ≅ Λ_Y`,
```
             ρ⁻¹                          ≅
M[2d] ─────────▶ M[2d] ⊗ᴸ Λ_Y ──────────────▶ M[2d] ⊗ᴸ (Λ_Y(d) ⊗ᴸ Λ_Y(-d))
          α⁻¹                                   (twisted trace) ⊗ 1                  λ
     ─────────▶ (M[2d] ⊗ᴸ Λ_Y(d)) ⊗ᴸ Λ_Y(-d) ───────────────────▶ Λ_Y ⊗ᴸ Λ_Y(-d) ────▶ Λ_Y(-d)
```
for `M = Ra_! Λ_X`. -/
noncomputable def untwistedSmoothTrace (γ : TateOrientation Λ a d) :
    ((R(a)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ X))⟦(2 * d : ℤ)⟧ ⟶
      tateObject Λ Y (-d) :=
  (derivedTensorRightUnitor _ Y _).inv ≫
    ((derivedTensor _ Y).obj _).map (constantComplexIsoTateObjectTensor Y d).hom ≫
      (derivedTensorAssociator _ Y _ _ _).inv ≫
        ((derivedTensor _ Y).map γ.twistedSmoothTrace).app _ ≫
          (derivedTensorLeftUnitor _ Y _).hom

/-- Blueprint `theorem-trace-isomorphism-top-degree`: Poincare duality conventions: trace and
trace-cup pairing.

The *untwisted trace map* `tr^{(-d)}_X : H^{2d}_c(X, Λ) ⟶ Λ(-d)` of a Tate orientation `γ`:
a compactly supported class `Λ_Y ⟶ (Ra_! Λ_X)[2d]` is composed with the untwisted smooth trace
(`AlgebraicGeometry.Etale.TateOrientation.untwistedSmoothTrace`). The target
`Hom(Λ_Y, Λ_Y(-d))` is `Λ(-d)` for `Y = Spec k`. It does not use properness; for `a` proper it
is the map `H^{2d}(X, Λ) ⟶ Λ(-d)` of `corollary-cup-product-pairing--1`, through
`AlgebraicGeometry.Etale.cohomologyAddEquivCompactSupport`. -/
noncomputable def untwistedTraceMap (γ : TateOrientation Λ a d) :
    ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶
        ((R(a)_![ModuleCat.{u + 1} Λ]).obj (constantComplex Λ X))⟦(2 * d : ℤ)⟧) →+
      ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ tateObject Λ Y (-d)) :=
  Preadditive.rightComp _ γ.untwistedSmoothTrace

/-- Blueprint `corollary-cup-product-pairing--1`: Trace and trace–cup pairing.

The *trace–cup pairing* of a Tate orientation `γ` of a proper morphism `a : X ⟶ Y`, for
complementary degrees `i + j = 2d`,

`⟨x, y⟩ = tr^{(-d)}_X(x ⌣ y) : H^i(X, Λ) × H^j(X, Λ) ⟶ Λ(-d)`,

where `x ⌣ y ∈ H^{2d}(X, Λ)` is the cup product (`AlgebraicGeometry.Etale.cupProduct`), read
in `H^{2d}_c(X, Λ)` through `Ra_! ≅ Ra_*`
(`AlgebraicGeometry.Etale.cohomologyAddEquivCompactSupport`), and `tr^{(-d)}_X` is the
untwisted trace map (`AlgebraicGeometry.Etale.TateOrientation.untwistedTraceMap`). The
identification `La^* Λ_Y ≅ Λ_X` is the one of the Tate twist datum
(`AlgebraicGeometry.Etale.leftDerivedUpperStarConstantComplexIso`). -/
noncomputable def traceCupPairing [IsProper a] (γ : TateOrientation Λ a d) (i j : ℤ)
    (hij : i + j = 2 * d) :
    ((𝟙_ (DerivedCategoryModule Λ X)) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦i⟧) →+
      ((𝟙_ (DerivedCategoryModule Λ X)) ⟶ (𝟙_ (DerivedCategoryModule Λ X))⟦j⟧) →+
        ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ tateObject Λ Y (-d)) :=
  (AddMonoidHom.compHom (γ.untwistedTraceMap.comp
    ((cohomologyAddEquivCompactSupport a (leftDerivedUpperStarConstantComplexIso Λ a)
      (2 * d)).toAddMonoidHom.comp
        (Preadditive.rightComp _ (eqToHom (by rw [hij])))))).comp (cupProduct _ i j)

end TateOrientation

end Etale

end AlgebraicGeometry
