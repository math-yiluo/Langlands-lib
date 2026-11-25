/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.GeometricFrobenius
public import WeilConjectures.AlgebraicGeometry.Morphisms.Frobenius
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar

/-!
# Scheme and geometric Frobenius of the purity datum

Let `k₀` be a finite field, `k̄` an algebraic closure and `f₀ : X₀ ⟶ Y₀` a morphism of
`k₀`-schemes, with base change `f : X ⟶ Y` to `k̄`. Two kinds of Frobenius act on `X` and `Y`:

* the *geometric-Galois* automorphisms `g_X = 𝟙 × Spec(γ)`, `g_Y = 𝟙 × Spec(γ)`
  (`AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius`), which form a *Cartesian* square
  with `f`;
* the *scheme Frobenius* endomorphisms `Φ_X = F_{X₀} × 𝟙`, `Φ_Y = F_{Y₀} × 𝟙`, base changes of the
  `#k₀`-power Frobenius endomorphisms of `X₀` and `Y₀`, which form a commutative (not Cartesian)
  square with `f`.

Since the absolute Frobenius acts trivially on the étale topos and
`Fr_X = Φ_X ∘ g_X⁻¹`, the derived pullbacks along `Φ_X` and `g_X` are identified by
comparison isomorphisms `κ_X : LΦ_X^* ≅ Lg_X^*`, compatible with `f`:
`Lf^* κ_Y = κ_X Lf^*`. The *purity Frobenius datum*
(`AlgebraicGeometry.Etale.PurityFrobeniusDatum`) consists of the Frobenius endomorphisms of the
models and such comparisons.

## Main definitions

- `AlgebraicGeometry.Etale.PurityFrobeniusDatum` (`sec-Weil-complexes`).
- `AlgebraicGeometry.Etale.PurityFrobeniusDatum.schemeFrobeniusX`,
  `AlgebraicGeometry.Etale.PurityFrobeniusDatum.schemeFrobeniusY`: `Φ_X` and `Φ_Y`.

## Main statements

- `AlgebraicGeometry.Etale.PurityFrobeniusDatum.commSq_schemeFrobenius`: the scheme-Frobenius
  square commutes. The geometric-Galois square is Cartesian by
  `AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap`.

## Implementation notes

The construction of the `#k₀`-power Frobenius endomorphism of a scheme is not available, so it
enters, as elsewhere in the repository, through the predicate
`AlgebraicGeometry.Scheme.Hom.IsFrobenius`, which determines it.

The comparisons `κ_X`, `κ_Y` are those of blueprint `lemma-scheme-frobenius-geometric-frobenius--1`,
built from the canonical trivialization `LF_X^* ≅ id` of the absolute Frobenius pullback
(`lemma-scheme-frobenius-geometric-frobenius--1`). Neither is formalised, so the comparisons are
fields of the datum, subject to their compatibility with `f`.
-/

@[expose] public section

universe u

open CategoryTheory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] {k₀ : Type u} [Field k₀] [Finite k₀] {X₀ Y₀ : Scheme.{u}}
  {aX : X₀ ⟶ Spec (.of k₀)} {aY : Y₀ ⟶ Spec (.of k₀)}

/-- Blueprint `sec-Weil-complexes`: Scheme and geometric Frobenius of the
purity datum.

For a morphism `f₀ : X₀ ⟶ Y₀` of schemes over a finite field `k₀` (`f₀ ≫ a_Y = a_X`), with base
change `f : X ⟶ Y` to the algebraic closure `k̄`, a *purity Frobenius datum* consists of

* the `#k₀`-power (scheme) Frobenius endomorphisms `F_{X₀}`, `F_{Y₀}` of the models, whose base
  changes are the scheme Frobenii `Φ_X`, `Φ_Y`
  (`AlgebraicGeometry.Etale.PurityFrobeniusDatum.schemeFrobeniusX`);
* comparison isomorphisms `κ_X : LΦ_X^* ≅ Lg_{X,γ}^*`, `κ_Y : LΦ_Y^* ≅ Lg_{Y,γ}^*` between the
  derived pullbacks along the scheme Frobenii and along the geometric-Galois automorphisms
  `g_{X,γ}`, `g_{Y,γ}` (`AlgebraicGeometry.Scheme.Hom.geometricGaloisFrobenius`);
* the compatibility `Lf^* κ_Y = κ_X Lf^*` of the comparisons with `f`, through the composition
  isomorphisms `LΦ_X^* Lf^* ≅ L(f ≫ Φ_Y)^* ≅ Lf^* LΦ_Y^*` and
  `Lf^* Lg_Y^* ≅ L(f ≫ g_Y)^* ≅ Lg_X^* Lf^*`.

The square formed by `f` with `g_γ` is Cartesian
(`AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap`), the one
formed with `Φ` commutes (`AlgebraicGeometry.Etale.PurityFrobeniusDatum.commSq_schemeFrobenius`).
In the blueprint the comparisons are those of `lemma-scheme-frobenius-geometric-frobenius--1`. -/
structure PurityFrobeniusDatum (f₀ : X₀ ⟶ Y₀) (hf₀ : f₀ ≫ aY = aX) where
  /-- The `#k₀`-power Frobenius endomorphism of `X₀`. -/
  frobX : X₀ ⟶ X₀
  isFrobenius_frobX : frobX.IsFrobenius (Nat.card k₀)
  /-- The `#k₀`-power Frobenius endomorphism of `Y₀`. -/
  frobY : Y₀ ⟶ Y₀
  isFrobenius_frobY : frobY.IsFrobenius (Nat.card k₀)
  /-- The comparison `κ_X : LΦ_X^* ≅ Lg_{X,γ}^*`. -/
  κX : L((Hom.geometricFiberMap frobX (isFrobenius_frobX.comp_eq aX))^*[ModuleCat.{u + 1} Λ]) ≅
    L((aX.geometricGaloisFrobenius.asIso.hom)^*[ModuleCat.{u + 1} Λ])
  /-- The comparison `κ_Y : LΦ_Y^* ≅ Lg_{Y,γ}^*`. -/
  κY : L((Hom.geometricFiberMap frobY (isFrobenius_frobY.comp_eq aY))^*[ModuleCat.{u + 1} Λ]) ≅
    L((aY.geometricGaloisFrobenius.asIso.hom)^*[ModuleCat.{u + 1} Λ])
  /-- The compatibility `Lf^* κ_Y = κ_X Lf^*`. -/
  κ_comm : ∀ K, ((leftDerivedUpperStarComp _ (Hom.geometricFiberMap frobX
      (isFrobenius_frobX.comp_eq aX)) (Hom.geometricFiberMap f₀ hf₀)).inv.app K ≫
      (leftDerivedUpperStarComp _ (Hom.geometricFiberMap f₀ hf₀) (Hom.geometricFiberMap frobY
        (isFrobenius_frobY.comp_eq aY))
        (Hom.geometricFiberMap frobX (isFrobenius_frobX.comp_eq aX) ≫
          Hom.geometricFiberMap f₀ hf₀) (by
          rw [← Hom.geometricFiberMap_comp, ← Hom.geometricFiberMap_comp]
          congr 1
          exact (isFrobenius_frobX.comp_eq_comp aX isFrobenius_frobY f₀).symm)).hom.app K) ≫
      (L((Hom.geometricFiberMap f₀ hf₀)^*[ModuleCat.{u + 1} Λ])).map (κY.hom.app K) ≫
      ((leftDerivedUpperStarComp _ (Hom.geometricFiberMap f₀ hf₀)
        aY.geometricGaloisFrobenius.asIso.hom
        (aX.geometricGaloisFrobenius.asIso.hom ≫ Hom.geometricFiberMap f₀ hf₀)
        (Hom.geometricFiberMap_comp_geometricGaloisFrobenius f₀ hf₀).symm).inv.app K ≫
      (leftDerivedUpperStarComp _ aX.geometricGaloisFrobenius.asIso.hom
        (Hom.geometricFiberMap f₀ hf₀)).hom.app K) =
    κX.hom.app ((L((Hom.geometricFiberMap f₀ hf₀)^*[ModuleCat.{u + 1} Λ])).obj K)

namespace PurityFrobeniusDatum

variable {Λ} {f₀ : X₀ ⟶ Y₀} {hf₀ : f₀ ≫ aY = aX} (D : PurityFrobeniusDatum Λ f₀ hf₀)

/-- The scheme Frobenius `Φ_X = F_{X₀} × 𝟙` of `X`. -/
noncomputable abbrev schemeFrobeniusX : aX.geometricFiber ⟶ aX.geometricFiber :=
  Hom.geometricFiberMap D.frobX (D.isFrobenius_frobX.comp_eq aX)

/-- The scheme Frobenius `Φ_Y = F_{Y₀} × 𝟙` of `Y`. -/
noncomputable abbrev schemeFrobeniusY : aY.geometricFiber ⟶ aY.geometricFiber :=
  Hom.geometricFiberMap D.frobY (D.isFrobenius_frobY.comp_eq aY)

/-- Blueprint `sec-Weil-complexes`: the square formed by `f` and the scheme
Frobenii commutes, `f ∘ Φ_X = Φ_Y ∘ f`; it is not Cartesian in general. (The square formed by
`f` and the geometric-Galois automorphisms is Cartesian:
`AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap`.) -/
theorem commSq_schemeFrobenius :
    CommSq D.schemeFrobeniusX (Hom.geometricFiberMap f₀ hf₀) (Hom.geometricFiberMap f₀ hf₀)
      D.schemeFrobeniusY := by
  constructor
  rw [← Hom.geometricFiberMap_comp, ← Hom.geometricFiberMap_comp]
  congr 1
  exact (D.isFrobenius_frobX.comp_eq_comp aX D.isFrobenius_frobY f₀).symm

end PurityFrobeniusDatum

end Etale

end AlgebraicGeometry
