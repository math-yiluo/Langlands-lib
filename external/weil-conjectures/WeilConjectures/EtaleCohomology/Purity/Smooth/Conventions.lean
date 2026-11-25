/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.SixFunctors.Etale.Derived.Coefficients
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.Shift
public import WeilConjectures.SixFunctors.Etale.Derived.TensorStructure
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriek
public import WeilConjectures.SixFunctors.Etale.Derived.UpperStarMonoidal
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat

/-!
# Conventions for smooth purity

This file fixes the twist-side vocabulary the smooth-purity chapter runs on: the Tate twist
`(m)`, the twist-and-shift `K ↦ K(m)[2m]`, the dualizing complex `ω_f = Rf^! Λ_Y`, and the
*section invariant* `𝒞(g, s) = Ls^* ω_g` of a morphism with a section. The constant complex
`Λ_X`, finite Tor amplitude, `D^b_{ctf}` and ⊗-invertibility are framework-level notions and
live in `WeilConjectures.SixFunctors.Etale.Derived.Coefficients`. The dualizing complex
`ω_f = Rf^! Λ_Y` is the framework's `AlgebraicGeometry.Etale.dualizingComplex` for
`A = ModuleCat Λ`, the constant complex `Λ_Y` being the monoidal unit.

The coefficient stage is the finite one: a commutative ring `Λ` and the abelian category
`ModuleCat Λ`, so that `D(X_ét, Λ)` is
`DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat Λ))`. Every statement of the chapter
assumes moreover that `Λ` is finite and that its exponent is invertible on the schemes in
sight (`AlgebraicGeometry.HasInvertibleExponent`); without that hypothesis smooth purity is
false, already for `Λ = ℤ/p` over a base of characteristic `p`. The remaining stages `𝒪_E`,
`E` and `ℚ̄_ℓ` are the derived-complete and rationalized categories of
`WeilConjectures.CategoryTheory.DerivedCategory.Complete`; purity is transported to them in
`WeilConjectures.EtaleCohomology.Purity.Smooth.Transport`.

## Implementation notes

The Tate twist is the one place where a genuinely missing object had to be named. Its
blueprint home is the framework chapter (`def:coefficient-twists`), not this block, and the
sheaf of roots of unity `μ_n` it is built from belongs to the Kummer block. It is therefore
taken as a *parameter*: `AlgebraicGeometry.Etale.HasTateTwist` bundles the twisting objects
`Λ_X(m)` with the identifications `Λ_X(0) ≅ Λ_X`, `Λ_X(m) ⊗ Λ_X(m') ≅ Λ_X(m + m')` and
`Lf^* Λ_Y(m) ≅ Λ_X(m)`, ⊗-invertibility, membership in `D^b_{ctf}`, and the coherences
between these identifications listed in "Additivity and pullback of twists" of the framework
chapter: unit and associativity laws, compatibility of pullback with composition, and
compatibility of pullback with products. The Kummer classes of units, the rank-one datum, are
cohomological data about `μ_n` rather than twist data; they are the separate class
`AlgebraicGeometry.Etale.HasKummerClass` of
`WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass`.

These fields do not determine the twisting objects: the untwisted datum `Λ_X(m) = Λ_X` and the
shifted datum `Λ_X(m) = Λ_X[-2m]`, with the evident identifications, satisfy all of them. A
statement that only manipulates twists formally — the twist-and-shift calculus, co-projection,
the pairings and traces built from a given orientation — holds for every twist datum and carries
`[HasTateTwist Λ]`. A statement comparing the twist with geometry — `Rs^! Λ(1)[2] ≅ Λ` for the
zero section of `𝔸¹`, affine-space and smooth purity, purity for regular immersions, Fourier
inversion — is false for those data and assumes moreover `[HasTateTwist.IsNormalized Λ]`
(`WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass`): the twist underlies Kummer
classes whose boundary for the coordinate of `𝔸¹_B` is the fundamental class of the zero
section, which forces `Λ_B(1) ≅ μ_n ⊗ Λ` on every `B` on which the exponent `n` of `Λ` is
invertible.

Invertibility is a field rather than a consequence of the zero and addition isomorphisms:
`Λ_X(m) ⊗ Λ_X(-m) ≅ Λ_X(0) ≅ Λ_X` is a two-line proof, but checking it forces the kernel to
unfold `AlgebraicGeometry.Etale.derivedTensor`, and that does not terminate in reasonable time.

## Main definitions

- `AlgebraicGeometry.Etale.HasTateTwist`: the Tate twist datum.
- `AlgebraicGeometry.Etale.tateObject`: the twisting object `Λ_X(m)`.
- `AlgebraicGeometry.Etale.tateTwist`: the twist `K ↦ K(m)`.
- `AlgebraicGeometry.Etale.twistShift`: `K ↦ K(m)[2m]`.
- `AlgebraicGeometry.Etale.shiftTateObjectAddIso`:
  `Λ_X(m)[2m] ⊗ Λ_X(m')[2m'] ≅ Λ_X(m + m')[2(m + m')]`.
- `AlgebraicGeometry.Etale.leftDerivedUpperStarConstantComplexIso`: `Lf^* Λ_Y ≅ Λ_X`.
- `AlgebraicGeometry.Etale.sectionInvariant`: `𝒞(g, s) = Ls^* ω_g`.

## Main statements

- `AlgebraicGeometry.Etale.isInvertible_tateObject`
- `AlgebraicGeometry.Etale.boundedConstructibleFiniteTor_tateObject`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `sk-def-purity-conv`: Purity conventions and the rank-one datum

A *Tate twist datum* for the coefficient ring `Λ`: for every scheme `X` and every `m : ℤ` a
⊗-invertible twisting object `Λ_X(m) ∈ D(X_ét, Λ)`, together with identifications

* `Λ_X(0) ≅ Λ_X` (`twistObjectZeroIso`),
* `Λ_X(m) ⊗ Λ_X(m') ≅ Λ_X(m + m')` (`twistObjectAddIso`),
* `Lf^* Λ_Y(m) ≅ Λ_X(m)` (`leftDerivedUpperStarTwistObjectIso`),

subject to the coherences of the framework's twists (`def:coefficient-twists`, "Additivity and
pullback of twists"): the zero-twist unit laws, the associativity law, compatibility of the
pullback identifications with composition of morphisms, and compatibility of the pullback
identifications with the products.

The identifications are *data*, not mere existence statements: the fundamental class of a
regular immersion is glued from local classes built out of them, and the gluing is only
meaningful because the coherences make the identifications used on overlapping pieces agree.

**The concrete model.** Let `ℓ` be the prime with `ℓ^N Λ = 0`, `N ≥ 1`, and `ℓ` invertible on
the schemes in sight. Then `Λ_X(1) = μ_{ℓ^N} ⊗_{ℤ/ℓ^N} Λ`, which does not depend on the choice
of `N`, `Λ_X(m) = Λ_X(1)^{⊗ m}` for `m ≥ 0` and `Λ_X(m) = RHom(Λ_X(-m), Λ_X)` for `m < 0`.
The sheaf of roots of unity belongs to the Kummer block and the twist itself to the framework
chapter, so the datum is taken as a parameter here rather than constructed. -/
-- TODO(unify): def:coefficient-twists
class HasTateTwist where
  /-- The twisting object `Λ_X(m)`. -/
  twistObject (X : Scheme.{u}) (m : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
  /-- `Λ_X(0)` is the constant complex. -/
  twistObjectZeroIso (X : Scheme.{u}) [HasInvertibleExponent Λ X] :
    twistObject X 0 ≅ constantComplex Λ X
  /-- `Λ_X(m) ⊗^L Λ_X(m') ≅ Λ_X(m + m')`, which is what makes `Λ(c)[2c]` the `c`-th tensor
  power of `Λ(1)[2]` in the Künneth iteration of `proposition-purity-vector-bundles`. -/
  twistObjectAddIso (X : Scheme.{u}) [HasInvertibleExponent Λ X] (m m' : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (twistObject X m)).obj (twistObject X m') ≅
      twistObject X (m + m')
  /-- The twist is compatible with pullback, `Lf^* Λ_Y(m) ≅ Λ_X(m)`; this is what makes the
  purity isomorphisms compatible with base change. -/
  leftDerivedUpperStarTwistObjectIso {X Y : Scheme.{u}} [HasInvertibleExponent Λ X]
      [HasInvertibleExponent Λ Y] (f : X ⟶ Y) (m : ℤ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).obj (twistObject Y m) ≅ twistObject X m
  /-- Every twisting object is ⊗-invertible, with inverse `Λ_X(-m)`. Mathematically this is
  a consequence of `twistObjectZeroIso` and `twistObjectAddIso`; it is a field of its own
  because deriving it forces the kernel to unfold `AlgebraicGeometry.Etale.derivedTensor`,
  which is prohibitively expensive. -/
  isInvertible_twistObject (X : Scheme.{u}) [HasInvertibleExponent Λ X] (m : ℤ) :
    DerivedCategory.isInvertible Λ X (twistObject X m)
  /-- Every twisting object lies in `D^b_{ctf}(X, Λ)`: in the concrete model `Λ_X(m)` is a lisse
  sheaf of free `Λ`-modules of rank one placed in degree zero. This is what lets the twists pass
  through the co-projection formula and the other finiteness statements of the chapter, all of
  which are stated on `D^b_{ctf}`. -/
  boundedConstructibleFiniteTor_twistObject (X : Scheme.{u}) [HasInvertibleExponent Λ X]
      (m : ℤ) :
    DerivedCategory.boundedConstructibleFiniteTor Λ X (twistObject X m)
  /-- Every twisting object is locally constant of rank one (`definition-tate-twists`):
  `Λ_X(m)` is a locally constant sheaf `L` of `Λ`-modules placed in degree zero, every stalk of
  which at a geometric point is free of rank one. In the concrete model
  `L = (μ_{ℓ^N} ⊗ Λ)^{⊗ m}`, respectively its `Λ`-dual for `m < 0`. -/
  exists_isLocallyConstantSheaf_twistObject (X : Scheme.{u}) [HasInvertibleExponent Λ X]
      (m : ℤ) :
    ∃ L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
        Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      Nonempty (twistObject X m ≅ (DerivedCategory.singleFunctor _ 0).obj L)
  /-- The left unit law: `Λ_X(0) ⊗ Λ_X(m) ≅ Λ_X(m)` is the left unitor, through
  `Λ_X(0) ≅ Λ_X`.

  ```
  Λ_X(0) ⊗ Λ_X(m) ──twistObjectAddIso──▶ Λ_X(0 + m) = Λ_X(m)
         │                                     ‖
  zero ⊗ 1                                     ‖
         ▼                                     ‖
   Λ_X ⊗ Λ_X(m) ───────────λ──────────────▶ Λ_X(m)
  ``` -/
  twistObjectAddIso_zero_left (X : Scheme.{u}) [HasInvertibleExponent Λ X] (m : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).map (twistObjectZeroIso X).hom).app
        (twistObject X m) ≫ (derivedTensorLeftUnitor _ X (twistObject X m)).hom =
      (twistObjectAddIso X 0 m).hom ≫ eqToHom (by rw [zero_add])
  /-- The right unit law: `Λ_X(m) ⊗ Λ_X(0) ≅ Λ_X(m)` is the right unitor, through
  `Λ_X(0) ≅ Λ_X`.

  ```
  Λ_X(m) ⊗ Λ_X(0) ──twistObjectAddIso──▶ Λ_X(m + 0) = Λ_X(m)
         │                                     ‖
  1 ⊗ zero                                     ‖
         ▼                                     ‖
   Λ_X(m) ⊗ Λ_X ───────────ρ──────────────▶ Λ_X(m)
  ``` -/
  twistObjectAddIso_zero_right (X : Scheme.{u}) [HasInvertibleExponent Λ X] (m : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (twistObject X m)).map
        (twistObjectZeroIso X).hom ≫ (derivedTensorRightUnitor _ X (twistObject X m)).hom =
      (twistObjectAddIso X m 0).hom ≫ eqToHom (by rw [add_zero])
  /-- The associativity law for the products of twisting objects.

  ```
  (Λ(a) ⊗ Λ(b)) ⊗ Λ(c) ───────α───────▶ Λ(a) ⊗ (Λ(b) ⊗ Λ(c))
          │                                      │
          ▼                                      ▼
   Λ(a + b) ⊗ Λ(c)                         Λ(a) ⊗ Λ(b + c)
          │                                      │
          ▼                                      ▼
   Λ((a + b) + c) ════════════════════════ Λ(a + (b + c))
  ``` -/
  twistObjectAddIso_assoc (X : Scheme.{u}) [HasInvertibleExponent Λ X] (a b c : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).map (twistObjectAddIso X a b).hom).app
        (twistObject X c) ≫ (twistObjectAddIso X (a + b) c).hom =
      (derivedTensorAssociator _ X (twistObject X a) (twistObject X b) (twistObject X c)).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (twistObject X a)).map
          (twistObjectAddIso X b c).hom ≫ (twistObjectAddIso X a (b + c)).hom ≫
            eqToHom (by rw [add_assoc])
  /-- The pullback identifications are compatible with composition: for `f : X ⟶ Y` and
  `g : Y ⟶ S`, `L(f ≫ g)^* Λ_S(m) ≅ Λ_X(m)` is the composite

  ```
  L(f ≫ g)^* Λ_S(m) ≅ Lf^* Lg^* Λ_S(m) ≅ Lf^* Λ_Y(m) ≅ Λ_X(m)
  ```

  through `AlgebraicGeometry.Etale.leftDerivedUpperStarComp`. -/
  leftDerivedUpperStarTwistObjectIso_comp {X Y S : Scheme.{u}} [HasInvertibleExponent Λ X]
      [HasInvertibleExponent Λ Y] [HasInvertibleExponent Λ S] (f : X ⟶ Y) (g : Y ⟶ S) (m : ℤ) :
    leftDerivedUpperStarTwistObjectIso (f ≫ g) m =
      (leftDerivedUpperStarComp (ModuleCat.{u + 1} Λ) f g).app (twistObject S m) ≪≫
        (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso (leftDerivedUpperStarTwistObjectIso g m) ≪≫
          leftDerivedUpperStarTwistObjectIso f m
  /-- The pullback identifications are compatible with the products of twisting objects, along
  the monoidal structure `Lf^* (K ⊗ M) ≅ Lf^* K ⊗ Lf^* M` of the derived pullback
  (`AlgebraicGeometry.Etale.leftDerivedUpperStarTensorIso`).

  ```
  Lf^*(Λ_Y(m) ⊗ Λ_Y(m')) ────≅────▶ Lf^* Λ_Y(m) ⊗ Lf^* Λ_Y(m') ───≅───▶ Λ_X(m) ⊗ Λ_X(m')
            │                                                               │
            ▼                                                               ▼
     Lf^* Λ_Y(m + m') ──────────────────────≅──────────────────────▶ Λ_X(m + m')
  ``` -/
  leftDerivedUpperStar_map_twistObjectAddIso {X Y : Scheme.{u}} [HasInvertibleExponent Λ X]
      [HasInvertibleExponent Λ Y] (f : X ⟶ Y) (m m' : ℤ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (twistObjectAddIso Y m m').hom ≫
        (leftDerivedUpperStarTwistObjectIso f (m + m')).hom =
      (leftDerivedUpperStarTensorIso (ModuleCat.{u + 1} Λ) f _ _).hom ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) X).map
          (leftDerivedUpperStarTwistObjectIso f m).hom).app _ ≫
          ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj (twistObject X m)).map
            (leftDerivedUpperStarTwistObjectIso f m').hom ≫ (twistObjectAddIso X m m').hom

variable [HasTateTwist Λ] (X : Scheme.{u})

/-- The twisting object `Λ_X(m) ∈ D(X_ét, Λ)` of a Tate twist datum. -/
noncomputable def tateObject (m : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  HasTateTwist.twistObject (Λ := Λ) X m

/-- Every Tate twisting object is ⊗-invertible, `Λ_X(m) ⊗^L Λ_X(-m) ≅ Λ_X`. -/
theorem isInvertible_tateObject [HasInvertibleExponent Λ X] (m : ℤ) :
    DerivedCategory.isInvertible Λ X (tateObject Λ X m) :=
  HasTateTwist.isInvertible_twistObject X m

/-- Every Tate twisting object lies in `D^b_{ctf}(X, Λ)`. -/
theorem boundedConstructibleFiniteTor_tateObject [HasInvertibleExponent Λ X] (m : ℤ) :
    DerivedCategory.boundedConstructibleFiniteTor Λ X (tateObject Λ X m) :=
  HasTateTwist.boundedConstructibleFiniteTor_twistObject X m

/-- Blueprint `def-pur-conventions`: Purity coefficient conventions

The Tate twist `(m) : D(X_ét, Λ) ⥤ D(X_ét, Λ)`, `K(m) = K ⊗^L_{Λ_X} Λ_X(m)`, tensoring with the
twisting object `Λ_X(m)`.

The purity conventions fix a finite coefficient ring `Λ` (the finite stage `A = A_{E,n}`), whose
exponent is invertible on the schemes in sight (`AlgebraicGeometry.HasInvertibleExponent`, i.e.
`ℓ ≠ p`), the operations `Lf^*`, `⊗^L`, `Rf_*`, `Rf_!`, `Rf^!` of the framework on the
categories `D(X_ét, Λ)`, `D^b_{ctf}(X, Λ)`, and the twists `K(m)` defined here; the dualizing
complex of `a : Y ⟶ Spec k` is `ω_{Y,Λ} = Ra^! Λ` (`AlgebraicGeometry.Etale.dualizingComplex`).
The normalization of geometric Frobenius on the twists (`q^{-m}` on `Λ(m)`) is
`prose-10-21` (`WeilConjectures.WeilSheaf.FrobeniusTwist`), and the
other coefficient stages `𝒪_E, E, ℚ̄_ℓ` are the transports of
`WeilConjectures.EtaleCohomology.Purity.Smooth.Transport`.

The blueprint states the conventions on the small pro-étale site; the purity chapter is
formalised on the small étale site, the pro-étale comparison
(`WeilConjectures.SixFunctors.ProEtale.Comparison`: `ν^*` is fully faithful on bounded below
complexes, and the pro-étale `Rf^!` is `ν_X^* ∘ Rf^! ∘ Rν_{Y,*}`,
`AlgebraicGeometry.ProEtale.rightDerivedUpperShriek`) transporting every statement on the
constructible categories. -/
noncomputable def tateTwist (m : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (derivedTensor (ModuleCat.{u + 1} Λ) X).flip.obj (tateObject Λ X m)

/-- The twist-and-shift functor `K ↦ K(m)[2m]` in which every purity statement is phrased. -/
noncomputable def twistShift (m : ℤ) :
    DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) ⥤
      DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  tateTwist Λ X m ⋙ shiftFunctor _ (2 * m)

/-- The identification `Λ_X(m)[2m] ⊗^L Λ_X(m')[2m'] ≅ Λ_X(m + m')[2(m + m')]`: the shifts are
moved out of the tensor product (`AlgebraicGeometry.Etale.derivedTensorShiftIso`) and the
twisting objects multiplied with `HasTateTwist.twistObjectAddIso`. All shifts are even, so no
sign is involved. -/
noncomputable def shiftTateObjectAddIso [HasInvertibleExponent Λ X] (m m' : ℤ) :
    ((derivedTensor (ModuleCat.{u + 1} Λ) X).obj ((tateObject Λ X m)⟦2 * m⟧)).obj
        ((tateObject Λ X m')⟦2 * m'⟧) ≅
      (tateObject Λ X (m + m'))⟦2 * (m + m')⟧ :=
  derivedTensorShiftIso _ _ _ (2 * m) (2 * m') ≪≫
    (shiftFunctor _ (2 * m + 2 * m')).mapIso (HasTateTwist.twistObjectAddIso X m m') ≪≫
      eqToIso (by simp only [tateObject, mul_add])

variable {Λ X} {Y : Scheme.{u}}

/-- The identification `Lf^* Λ_Y(m) ≅ Λ_X(m)` of the Tate twist datum. -/
noncomputable def leftDerivedUpperStarTateObjectIso [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) (m : ℤ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).obj (tateObject Λ Y m) ≅ tateObject Λ X m :=
  HasTateTwist.leftDerivedUpperStarTwistObjectIso f m

omit [HasTateTwist Λ] in
variable (Λ) in
/-- The identification `Lf^* Λ_Y ≅ Λ_X` of the constant complexes: the counit `η` of the oplax
monoidal structure of the derived pullback (`AlgebraicGeometry.Etale.leftDerivedUpperStarMonoidal`),
which is an isomorphism. It does not depend on a Tate twist datum. -/
noncomputable def leftDerivedUpperStarConstantComplexIso (f : X ⟶ Y) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).obj (constantComplex Λ Y) ≅ constantComplex Λ X :=
  letI := leftDerivedUpperStarOplaxMonoidal (ModuleCat.{u + 1} Λ) f
  haveI := isIso_leftDerivedUpperStarOplaxMonoidal_η (ModuleCat.{u + 1} Λ) f
  asIso (Functor.OplaxMonoidal.η (L((f)^*[ModuleCat.{u + 1} Λ])))

variable (Λ) in
/-- The identification `Le^* (Λ_X(m)[2m]) ≅ Λ_U(m)[2m]`, through the shift compatibility of
`Le^*` and the identification `Le^* Λ_X(m) ≅ Λ_U(m)` of the Tate twist datum. -/
noncomputable def leftDerivedUpperStarTateShiftIso [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) (m : ℤ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).obj ((tateObject Λ Y m)⟦2 * m⟧) ≅
      (tateObject Λ X m)⟦2 * m⟧ :=
  ((L((f)^*[ModuleCat.{u + 1} Λ])).commShiftIso (2 * m)).app _ ≪≫
    (shiftFunctor _ (2 * m)).mapIso (leftDerivedUpperStarTateObjectIso f m)

omit [HasTateTwist Λ] in
variable (Λ) in
/-- The identification `Lc^* Lg^* Λ_Y ≅ Λ_X` for the chosen compactification `(c, g)` of
`f : X ⟶ Y`, through `AlgebraicGeometry.Etale.leftDerivedUpperStarConstantComplexIso`. -/
noncomputable def compactificationConstantComplexIso (f : X ⟶ Y) [HasCompactification f] :
    (L(((HasCompactification.compactification f).i)^*[ModuleCat.{u + 1} Λ])).obj
        ((L(((HasCompactification.compactification f).g)^*[ModuleCat.{u + 1} Λ])).obj
          (constantComplex Λ Y)) ≅ constantComplex Λ X :=
  (L(((HasCompactification.compactification f).i)^*[ModuleCat.{u + 1} Λ])).mapIso
      (leftDerivedUpperStarConstantComplexIso Λ _) ≪≫
    leftDerivedUpperStarConstantComplexIso Λ _

variable (Λ X)

/-- Blueprint `lemma-section-normal-bundle--1`: Section invariant

Part of blueprint `sk-def-purity-conv`. The *section invariant*
`𝒞(g, s) = Ls^* ω_g = Ls^* Rg^! Λ_B` of a morphism `g : V ⟶ B` together with a section
`s : B ⟶ V`. For `g` smooth of pure relative dimension `d` with `s` a
closed section, smooth purity identifies it with `Λ_B(d)[2d]`; the deformation to the normal
cone of the section reduces the general case to the standard pair `(𝔸^d_B → B, 0)`. -/
noncomputable def sectionInvariant [Finite Λ] {V B : Scheme.{u}} (g : V ⟶ B)
    [HasCompactification g]
    (s : B ⟶ V) : DerivedCategory (Sheaf B.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :=
  (L((s)^*[ModuleCat.{u + 1} Λ])).obj (dualizingComplex Λ g)

end Etale

end AlgebraicGeometry
