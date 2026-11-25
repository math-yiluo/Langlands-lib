/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.Monoidal.UnitComparison
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Basic
public import WeilConjectures.SixFunctors.Etale.Derived.WeilComplexDual
public import WeilConjectures.SixFunctors.Etale.Derived.WeilFrobeniusAdjunction

/-!
# Strict Weil data and the Tate datum

Let `f : X ⟶ Y` be the base change to `k̄` of a morphism `f₀ : X₀ ⟶ Y₀` of schemes over a finite
field, smooth of relative dimension `d`, and let `g_X`, `g_Y` be the geometric-Frobenius
automorphisms of `X` and `Y`, which form a cartesian square `g_X ≫ f = f ≫ g_Y`
(`AlgebraicGeometry.Scheme.Hom.isPullback_geometricGaloisFrobenius_geometricFiberMap`). Following
blueprint `definition-weil-structure--1`, a *strict geometric-Weil datum* on `K ∈ D(Y_ét, Λ)` is an
isomorphism `φ_K : Lg_Y^* K ≅ K`, a Weil structure in the sense of `definition-weil-structure`
(`AlgebraicGeometry.Etale.WeilComplex`). This file constructs the Weil data that the smooth purity
chapter transports through the purity isomorphism:

* the *Tate datum* `τ_r : Lg^* Λ_Y(r) ≅ Λ_Y(r)` of the Tate twist
  (`AlgebraicGeometry.Etale.tateWeilDatum`): the identification of the twist datum with its
  pullback along `g`;
* the Tate line `(Λ_X(r), τ_r)` as a strict Weil complex
  (`AlgebraicGeometry.Etale.WeilComplex.tate`),
  the twisted dual `(K^∨(r), φ_{K^∨} ⊗ τ_r)` of a strict Weil complex
  (`AlgebraicGeometry.Etale.WeilComplex.twistedDual`), and the identification of `τ_0` with the
  canonical Weil structure `φ_Λ` of `Λ_X`
  (`AlgebraicGeometry.Etale.leftDerivedUpperStar_map_twistObjectZeroIso_hom`);
* the datum `φ^pur_{f,K}` on the source `Lf^* K(d)[2d]` of smooth purity
  (`AlgebraicGeometry.Etale.smoothPurityWeilDatum`): the base change identification followed by
  `Lf^* φ_K`, the Tate datum `τ_d` entering through the base change identification;
* the datum `φ^!_{f,K}` on the exceptional inverse image `Rf^! K`
  (`AlgebraicGeometry.Etale.upperShriekWeilDatum`): the smooth pullback exchange
  `Ex^{!,sm}_{f,g_Y,K}` of `proposition-compatibility-purity-base-change--1` followed by
  `Rf^!(φ_K)`.

The scheme-Frobenius form `u_K = φ_K ∘ κ_{Y,K}` of a datum is
`AlgebraicGeometry.Etale.schemeFrobeniusForm` in
`WeilConjectures.SixFunctors.Etale.Derived.SchemeGaloisComparison`, together with the
comparison `κ : LΦ^* ≅ Lg^*` of the scheme and the geometric Galois Frobenius pullbacks.

## Implementation notes

The constructions only use the commutativity of the squares (and their cartesianness for the
smooth pullback exchange), so they are stated for arbitrary endomorphisms `g_X`, `g_Y` forming
such a square; the geometric-Frobenius automorphisms are the case of interest. As for
`AlgebraicGeometry.Etale.smoothPullbackExchange`, the identifications `θ` of the dualizing complex
and the tensor formulas `φ` are arguments of the construction of `φ^!_{f,K}`.
-/

@[expose] public section

universe u' u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Generic

variable (A : Type u') [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {X Y : Scheme.{u}} (f : X ⟶ Y)
  [(f)^*[A].PreservesFlat]

/-- Let `Z ≅ Λ_Y` and `Z' ≅ Λ_X` be objects identified with the units, with products
`Z ⊗ᴸ Z ⟶ Z` and `Z' ⊗ᴸ Z' ⟶ Z'` satisfying the left unit law, and `τ : Lf^* Z ≅ Z'` compatible
with the products. Then `τ` corresponds to the canonical identification `Lf^* Λ_Y ≅ Λ_X`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`) under the identifications with the
units. The statement is phrased with the derived tensor product `-⊗ᴸ-`, so that it can be
instantiated at `A = ModuleCat Λ`
(`CategoryTheory.MonoidalCategory.map_hom_comp_eq_of_whiskerRight_comp_leftUnitor`). -/
lemma leftDerivedUpperStar_map_hom_comp_unitIso_hom_eq
    {Z : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology A)}
    {Z' : _root_.DerivedCategory (Sheaf X.smallEtaleTopology A)} (zY : Z ≅ 𝟙_ _) (zX : Z' ≅ 𝟙_ _)
    (addY : ((derivedTensor A Y).obj Z).obj Z ⟶ Z)
    (addX : ((derivedTensor A X).obj Z').obj Z' ⟶ Z') (τ : L((f)^*[A]).obj Z ≅ Z')
    (hY : ((derivedTensor A Y).map zY.hom).app Z ≫ (derivedTensorLeftUnitor A Y Z).hom = addY)
    (hX : ((derivedTensor A X).map zX.hom).app Z' ≫ (derivedTensorLeftUnitor A X Z').hom = addX)
    (hadd : L((f)^*[A]).map addY ≫ τ.hom =
      (leftDerivedUpperStarTensorIso A f Z Z).hom ≫ ((derivedTensor A X).map τ.hom).app _ ≫
        ((derivedTensor A X).obj Z').map τ.hom ≫ addX) :
    L((f)^*[A]).map zY.hom ≫ (leftDerivedUpperStarUnitIso A f).hom = τ.hom ≫ zX.hom :=
  MonoidalCategory.map_hom_comp_eq_of_whiskerRight_comp_leftUnitor L((f)^*[A])
    (fun K M ↦ (leftDerivedUpperStarTensorIso A f K M).hom)
    (fun g M ↦ leftDerivedUpperStarTensorIso_hom_naturality_left f g M)
    (leftDerivedUpperStarUnitIso A f).hom
    (leftDerivedUpperStarTensorComparison_leftUnitor_hom A f Z)
    zY zX addY addX τ hY hX hadd

end Generic

section Tate

variable (Λ : Type (u + 1)) [CommRing Λ] [HasTateTwist Λ] {X : Scheme.{u}}
  [HasInvertibleExponent Λ X]

/-- Blueprint `definition-weil-structure--1`: Strict Weil data and the Tate datum.

The *Tate datum* `τ_r : Lg^* Λ_X(r) ≅ Λ_X(r)` on the Tate twist `Λ_X(r)` for an endomorphism
`g` of `X` (for `g = g_{X,γ}` the geometric-Frobenius automorphism): the identification
`Lg^* Λ_X(r) ≅ Λ_X(r)` of the Tate twist datum
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTateObjectIso`). This is the canonical Weil
structure of the twist, the twist normalization of `prose-10-21`,
on which geometric Frobenius acts by `q^{-r}`. -/
noncomputable def tateWeilDatum (g : X ⟶ X) (r : ℤ) :
    (L((g)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ X r) ≅ tateObject Λ X r :=
  leftDerivedUpperStarTateObjectIso g r

/-- Transporting the identifications `Lf^* Λ_Y(m) ≅ Λ_X(m)` along an equality `m = m'`. -/
lemma leftDerivedUpperStarTwistObjectIso_eqToHom {Y : Scheme.{u}} [HasInvertibleExponent Λ Y]
    (f : X ⟶ Y) {m m' : ℤ} (h : m = m') :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map
        (eqToHom (congrArg (HasTateTwist.twistObject (Λ := Λ) Y) h)) ≫
        (HasTateTwist.leftDerivedUpperStarTwistObjectIso (Λ := Λ) f m').hom =
      (HasTateTwist.leftDerivedUpperStarTwistObjectIso (Λ := Λ) f m).hom ≫
        eqToHom (congrArg (HasTateTwist.twistObject (Λ := Λ) X) h) := by
  subst h
  simp

section ZeroTwist

variable {Y : Scheme.{u}} [HasInvertibleExponent Λ Y] (f : X ⟶ Y)

private lemma map_twistObjectAddIso_zero_zero :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map ((HasTateTwist.twistObjectAddIso (Λ := Λ) Y 0 0).hom ≫
        eqToHom (congrArg (HasTateTwist.twistObject (Λ := Λ) Y) (add_zero 0))) ≫
        (HasTateTwist.leftDerivedUpperStarTwistObjectIso (Λ := Λ) f 0).hom =
      (leftDerivedUpperStarTensorIso _ f _ _).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).map
          (HasTateTwist.leftDerivedUpperStarTwistObjectIso (Λ := Λ) f 0).hom).app _ ≫
          ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (HasTateTwist.twistObject X 0)).map
            (HasTateTwist.leftDerivedUpperStarTwistObjectIso (Λ := Λ) f 0).hom ≫
            (HasTateTwist.twistObjectAddIso (Λ := Λ) X 0 0).hom ≫
              eqToHom (congrArg (HasTateTwist.twistObject (Λ := Λ) X) (add_zero 0)) := by
  rw [Functor.map_comp, Category.assoc,
    leftDerivedUpperStarTwistObjectIso_eqToHom Λ f (add_zero 0),
    ← Category.assoc, HasTateTwist.leftDerivedUpperStar_map_twistObjectAddIso]
  simp only [Category.assoc]

/-- Blueprint `definition-weil-structure`: the canonical Weil structure `φ_Λ` of `Λ_T` is the Tate
datum `τ_0`.

For every morphism `f : X ⟶ Y` the identification `Lf^* Λ_Y(0) ≅ Λ_X(0)` of the twist datum
corresponds to the canonical identification `ε : Lf^* Λ_Y ≅ Λ_X`
(`AlgebraicGeometry.Etale.leftDerivedUpperStarUnitIso`) under `Λ(0) ≅ Λ`
(`HasTateTwist.twistObjectZeroIso`). In particular, for an endomorphism `g` the Tate datum `τ_0`
(`AlgebraicGeometry.Etale.tateWeilDatum`) is the canonical Weil structure `φ_Λ` of `Λ_X`. This
holds for every Tate twist datum: both identifications are compatible with the unit law
`Λ(0) ⊗ Λ(0) ≅ Λ(0)` of the twist datum
(`CategoryTheory.MonoidalCategory.map_hom_comp_eq_of_whiskerRight_comp_leftUnitor`). -/
theorem leftDerivedUpperStar_map_twistObjectZeroIso_hom :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (HasTateTwist.twistObjectZeroIso (Λ := Λ) Y).hom ≫
        (leftDerivedUpperStarUnitIso _ f).hom =
      (leftDerivedUpperStarTateObjectIso f 0).hom ≫
        (HasTateTwist.twistObjectZeroIso (Λ := Λ) X).hom :=
  leftDerivedUpperStar_map_hom_comp_unitIso_hom_eq _ f _ _ _ _ _
    (HasTateTwist.twistObjectAddIso_zero_left (Λ := Λ) Y 0)
    (HasTateTwist.twistObjectAddIso_zero_left (Λ := Λ) X 0) (map_twistObjectAddIso_zero_zero Λ f)

end ZeroTwist

namespace WeilComplex

variable {Λ} [Finite Λ] (g : X ≅ X)

variable (Λ) in
/-- Blueprint `definition-weil-structure`: the *Tate line* `(Λ_X(r), τ_r)` as a strict Weil
complex, for an automorphism `g` of `X` (for `g = g_{X,γ}` the geometric-Frobenius
automorphism): the Tate twist `Λ_X(r) ∈ Dctf(X, Λ)` with its canonical Weil structure, the Tate
datum `τ_r : Lg^* Λ_X(r) ≅ Λ_X(r)` (`AlgebraicGeometry.Etale.tateWeilDatum`). -/
noncomputable def tate (r : ℤ) : WeilComplex (ModuleCat.{u + 1} Λ) g where
  obj := ⟨tateObject Λ X r, boundedConstructibleFiniteTor_tateObject Λ X r⟩
  frobenius := ObjectProperty.isoMk _ (tateWeilDatum Λ g.hom r)

omit [Finite Λ] in
lemma tate_frobenius_hom_hom (r : ℤ) :
    (tate Λ g r).frobenius.hom.hom = (tateWeilDatum Λ g.hom r).hom :=
  rfl

variable {g} {k : Type u} [Field k] [IsAlgClosed k] (aX : X ⟶ Spec (.of k))
  [LocallyOfFiniteType aX] [QuasiCompact aX]

/-- Blueprint `theorem-poincare-duality-frobenius--1`: Dual and Tate Weil data.

The *twisted dual* `(K^∨(r), φ_{K^∨(r)})` of a strict Weil complex `(K, φ_K)`: the coefficient
dual `K^∨ = RHom(K, Λ_X)` with the contragredient datum `φ_{K^∨}`
(`AlgebraicGeometry.Etale.contragredientWeilDatum`), twisted by the Tate line, with the datum
`φ_{K^∨(r)} = φ_{K^∨} ⊗ τ_r`
(`AlgebraicGeometry.Etale.WeilComplex.twistedCoefficientDual_frobenius_hom_hom`). -/
noncomputable def twistedDual (K : WeilComplex (ModuleCat.{u + 1} Λ) g) (r : ℤ) :
    WeilComplex (ModuleCat.{u + 1} Λ) g :=
  twistedCoefficientDual aX K (tate Λ g r)

end WeilComplex

end Tate

section Purity

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {d : ℕ} (f : X ⟶ Y) [HasCompactification f] [HasInvertibleExponent Λ X] {gX : X ⟶ X}
  {gY : Y ⟶ Y}

variable (d) in
/-- Blueprint `definition-weil-structure--1`: Strict Weil data and the Tate datum.

The datum `φ^pur_{f,K}` induced on the source `Lf^* K(d)[2d]` of smooth purity by a strict Weil
datum `φ_K : Lg_Y^* K ≅ K` (more generally by any Weil datum `φ_K : Lg_Y^* K ⟶ K`), for a
commutative square `g_X ≫ f = f ≫ g_Y`:
```
                          ≅                                   Lf^* φ_K ⊗ τ_d
  Lg_X^*(Lf^* K(d)[2d]) ────▶ Lf^* Lg_Y^* K ⊗ Lg_X^* Λ_X(d)[2d] ──────────────▶ Lf^* K(d)[2d].
```
The first arrow moves `Lg_X^*` through the twist and shift and identifies
`Lg_X^* Lf^* ≅ Lf^* Lg_Y^*` along the square, the Tate datum `τ_d` of `Λ_X(d)`
(`AlgebraicGeometry.Etale.tateWeilDatum`) being applied on the twisting factor
(`AlgebraicGeometry.Etale.leftDerivedUpperStarTwistShiftBaseChangeIso`); the second applies
`Lf^* φ_K`. -/
noncomputable def smoothPurityWeilDatum (sq : CommSq gX f f gY)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K) :
    (L((gX)^*[ModuleCat.{u + 1} Λ])).obj
        ((twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)) ⟶
      (twistShift Λ X d).obj ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K) :=
  (leftDerivedUpperStarTwistShiftBaseChangeIso Λ d f sq K).hom ≫
    (twistShift Λ X d).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map φ)

/-- Blueprint `definition-weil-structure--1`: Strict Weil data and the Tate datum.

The datum `φ^!_{f,K}` induced on the exceptional inverse image `Rf^! K` by a strict Weil datum
`φ_K : Lg_Y^* K ≅ K` (more generally by any Weil datum `φ_K : Lg_Y^* K ⟶ K`), for a cartesian
square `g_X ≫ f = f ≫ g_Y`:
```
                Ex^{!,sm}_{f,g_Y,K}                 Rf^!(φ_K)
  Lg_X^* Rf^! K ───────────────────▶ Rf^! Lg_Y^* K ──────────▶ Rf^! K,
```
the smooth pullback exchange of `proposition-compatibility-purity-base-change--1`
(`AlgebraicGeometry.Etale.smoothPullbackExchange`) followed by `Rf^!(φ_K)`. The identifications
`θ : ω_f ≅ Λ_X(d)[2d]` and the tensor formulas `φf : Lf^* K ⊗ ω_f ≅ Rf^! K`,
`φf' : Lf^* Lg_Y^* K ⊗ ω_f ≅ Rf^! Lg_Y^* K` that the exchange is built from are arguments, as in
`AlgebraicGeometry.Etale.smoothPullbackExchange`; the result is the blueprint's canonical
`φ^!_{f,K}` only when these are the canonical identifications. -/
noncomputable def upperShriekWeilDatum (sq : IsPullback gX f f gY)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (θ : dualizingComplex Λ f ≅
      (twistShift Λ X d).obj (constantComplex Λ X))
    (φf : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
          (dualizingComplex Λ f) ≅
      (rightDerivedUpperShriek Λ f).obj K)
    (φf' : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj ((L((gY)^*[ModuleCat.{u + 1} Λ])).obj K))).obj
          (dualizingComplex Λ f) ≅
      (rightDerivedUpperShriek Λ f).obj
        ((L((gY)^*[ModuleCat.{u + 1} Λ])).obj K)) :
    (L((gX)^*[ModuleCat.{u + 1} Λ])).obj
        ((rightDerivedUpperShriek Λ f).obj K) ⟶
      (rightDerivedUpperShriek Λ f).obj K :=
  (smoothPullbackExchange Λ f sq K θ φf θ φf').hom ≫
    (rightDerivedUpperShriek Λ f).map φ

/-- The datum `φ^!_{f,K}` corresponds to the datum `φ^pur_{f,K}` under the smooth purity
isomorphism `γ_{f,K} : Lf^* K(d)[2d] ≅ Rf^! K` (`AlgebraicGeometry.Etale.smoothPurityIso`) built
from `θ` and `φf`, provided the purity isomorphism of `Lg_Y^* K` built from `θ` and `φf'` is
compatible with `φ_K` (that is, `γ_{f,-}` is natural along `φ_K`): `γ_{f,K}` is then a morphism
of Weil objects. -/
theorem smoothPurityIso_hom_comp_upperShriekWeilDatum (sq : IsPullback gX f f gY)
    {K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (φ : (L((gY)^*[ModuleCat.{u + 1} Λ])).obj K ⟶ K)
    (θ : dualizingComplex Λ f ≅
      (twistShift Λ X d).obj (constantComplex Λ X))
    (φf : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj K)).obj
          (dualizingComplex Λ f) ≅
      (rightDerivedUpperShriek Λ f).obj K)
    (φf' : ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj
        ((L((f)^*[ModuleCat.{u + 1} Λ])).obj ((L((gY)^*[ModuleCat.{u + 1} Λ])).obj K))).obj
          (dualizingComplex Λ f) ≅
      (rightDerivedUpperShriek Λ f).obj
        ((L((gY)^*[ModuleCat.{u + 1} Λ])).obj K))
    (hφ : (twistShift Λ X d).map ((L((f)^*[ModuleCat.{u + 1} Λ])).map φ) ≫
        (smoothPurityIso Λ f K θ φf).hom =
      (smoothPurityIso Λ f _ θ φf').hom ≫ (rightDerivedUpperShriek _ f).map φ) :
    (L((gX)^*[ModuleCat.{u + 1} Λ])).map (smoothPurityIso Λ f K θ φf).hom ≫
        upperShriekWeilDatum Λ f sq φ θ φf φf' =
      smoothPurityWeilDatum Λ d f sq.toCommSq φ ≫ (smoothPurityIso Λ f K θ φf).hom := by
  rw [upperShriekWeilDatum, reassoc_of%
    leftDerivedUpperStar_map_comp_smoothPullbackExchange_hom Λ f sq K θ φf θ φf',
    smoothPurityWeilDatum, Category.assoc]
  exact congrArg (_ ≫ ·) hφ.symm

end Purity

end Etale

end AlgebraicGeometry
