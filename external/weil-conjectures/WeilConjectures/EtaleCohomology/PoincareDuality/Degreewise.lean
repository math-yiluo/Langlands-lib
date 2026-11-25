/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Perfect
public import WeilConjectures.EtaleCohomology.PoincareDuality.Pairing
public import WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness
public import WeilConjectures.SixFunctors.Etale.Derived.Finiteness.CompactSupport
public import WeilConjectures.SixFunctors.Etale.Derived.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.LowerStarProjection

/-!
# The degreewise Poincaré pairings and degreewise duality over a field

Let `γ` be a Tate orientation of `a : X ⟶ Y` of relative dimension `d`, and `K ∈ D(X_ét, Λ)`.
The derived Poincaré pairing

`β_K : RΓ_c(X, K) ⊗ᴸ RΓ(X, K^∨(d))[2d] ⟶ Λ`

(`AlgebraicGeometry.Etale.TateOrientation.poincarePairing`) has degree zero. With the shift
convention `Hʳ(C[m]) = Hʳ⁺ᵐ(C)`, its degree-zero part pairs `Hⁱ_c(X, K)` with
`H⁻ⁱ(RΓ(X, K^∨(d))[2d]) = H^{2d-i}(X, K^∨(d))`, giving the pairings

`⟨-, -⟩ᵢ : Hⁱ_c(X, K) × H^{2d-i}(X, K^∨(d)) ⟶ Λ`.

Eliminating the invertible twist `Λ(d)` of the second factor, the same morphism gives the
line-valued pairings `Hⁱ_c(X, K) × H^{2d-i}(X, K^∨) ⟶ Λ(-d)`.

As in `WeilConjectures.EtaleCohomology.PoincareDuality.TraceCup`, cohomology classes are
morphisms out of the unit: a class in `Hⁿ_c(X, K)` is a morphism `Λ_Y ⟶ (Ra_! K)[n]` and a
class in `Hⁿ(X, M)` a morphism `Λ_Y ⟶ (Ra_* M)[n]` of `D(Y_ét, Λ)`; for `Y = Spec k` with `k`
separably closed these are the cohomology groups, and `Hom(Λ_Y, Λ_Y(m)) = Λ(m)`.

## Degreewise duality

Let `k` be a separably closed field, `a : X ⟶ Spec k` a morphism locally of finite type
admitting a compactification, `Λ` a finite field whose characteristic is invertible on `X`,
with a Tate twist datum, and `γ` a Tate orientation of `a` of relative dimension `d`. For
`K ∈ D^b_{ctf}(X, Λ)` perfect over `Λ_X`, the derived Poincaré duality
`RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`
(`AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing`) gives, in every
degree `i`, an isomorphism of finite-dimensional `Λ`-vector spaces

`H^{2d-i}(X, K^∨(d)) ≅ H^i_c(X, K)^∨`,

and for proper `a` the same with `H_c` replaced by `H`.

## Main definitions

All of them are blueprint `corollary-degreewise-duality-over-fields--1`.

- `AlgebraicGeometry.Etale.TateOrientation.degreeZeroPairing`: the degree-zero part of `β_K`,
  pairing `Hⁱ_c(X, K)` with `H⁻ⁱ(RΓ(X, K^∨(d))[2d])`.
- `AlgebraicGeometry.Etale.TateOrientation.degreewisePairing`: the pairings
  `⟨-, -⟩ᵢ : Hⁱ_c(X, K) × Hʲ(X, K^∨(d)) ⟶ Λ` for `i + j = 2d`.
- `AlgebraicGeometry.Etale.TateOrientation.untwistedDegreewisePairing`: the line-valued
  pairings `Hⁱ_c(X, K) × Hʲ(X, K^∨) ⟶ Λ(-d)` for `i + j = 2d`.

## Main statements

- `AlgebraicGeometry.Etale.TateOrientation.degreewisePairing_apply`: `⟨x, y⟩ᵢ` is the
  degree-zero part of `β_K` evaluated on `x` and on `y` read in `H⁻ⁱ(RΓ(X, K^∨(d))[2d])`.
- `AlgebraicGeometry.Etale.nonempty_iso_rightDerivedGlobalSections_of_isPerfectPairing`: over a
  separably closed field, derived global sections carry perfect pairings to dualities
  (from blueprint `theorem-global-verdier-duality`).
- `AlgebraicGeometry.Etale.TateOrientation.degreewise_duality`
(`corollary-degreewise-duality-over-fields`,
  `corollary-degreewise-duality-over-fields--1`): degreewise duality over a field.
- `AlgebraicGeometry.Etale.TateOrientation.degreewise_duality_of_isProper`
  (`theorem-poincare-duality--8`, degreewise part): the same for proper `X`, with ordinary
  cohomology.

## Implementation notes

The Hom groups of `D(Y_ét, Λ)` carry no `Λ`-module structure in the repository, so the
pairings are biadditive rather than `Λ`-bilinear. The complementary degrees are two integers
`i j` with `i + j = 2d`, `2d - (2d - i)` not being definitionally `i`.

The cohomology groups are the cohomology of the derived global sections
`AlgebraicGeometry.Etale.rightDerivedGlobalSections`, which land in the derived category of
`Λ`-modules; `H^i_c(X, K)` is `AlgebraicGeometry.Etale.compactlySupportedCohomology`.

The blueprint asserts that the adjoint `H^{2d-i}(X, K^∨(d)) ⟶ H^i_c(X, K)^∨` of the degreewise
pairing `⟨-, -⟩_i` is an isomorphism. The pairing
`AlgebraicGeometry.Etale.TateOrientation.degreewisePairing` is stated on classes
`Λ_Y ⟶ (Ra_! K)[i]`; comparing it with the cohomology of `RΓ(Spec k, -)` needs the lax monoidal
structure of `RΓ(Spec k, -)`, which the repository does not have. The degreewise duality is
therefore only proved in a non-canonical form, as an abstract isomorphism `Nonempty (_ ≅ _)`.
Between finite-dimensional spaces this only says that the two dimensions agree; it does not
close the blueprint statement that the adjoint of `⟨-, -⟩_i` is an isomorphism. The line-valued
form with values in `Λ(-d)` is not stated separately.

TODO: once `RΓ(Spec k, -)` is lax monoidal, restate the degreewise duality as `IsIso` of the
adjoint of `⟨-, -⟩_i`, from a canonical form of
`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedGlobalSections_of_isPerfectPairing`.

The field stages of the blueprint are `E` and `ℚ̄_ℓ`. The derived duality is available here
only at finite coefficients (the projection formula is stated there), so the field is a finite
field `Λ`, for example `A_{E,1} = 𝒪_E/𝔪_E`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

section General

variable {A : Type*} [Category.{u + 1} A] [Abelian A] [IsGrothendieckAbelian.{u + 1} A]
  [MonoidalCategory A] [MonoidalPreadditive A] [SymmetricCategory A] [MonoidalClosed A]
  [Abelian.HasFunctorialFlatResolution A] {Y : Scheme.{u}}

/-- The derived category `D(Y_ét, A)` of `A`-valued étale sheaves on `Y`. -/
local notation "𝐃(" Y ", " A ")" =>
  _root_.DerivedCategory (Sheaf (Scheme.smallEtaleTopology Y) A)

/-- The degree-zero part of a pairing `β : C ⊗ᴸ D ⟶ Λ_Y`, applied to classes
`x : Λ_Y ⟶ C[i]` and `y : S ⟶ D[-i]`:
```
      λ⁻¹               x ⊗ y                     ≅                 ≅            β
S ─────────▶ Λ_Y ⊗ᴸ S ────────▶ C[i] ⊗ᴸ D[-i] ─────▶ (C ⊗ᴸ D)[i - i] ─────▶ C ⊗ᴸ D ─────▶ Λ_Y
``` -/
noncomputable def degreeZeroPairingOfPairingAux {C D S : 𝐃(Y, A)}
    (β : ((derivedTensor A Y).obj C).obj D ⟶ 𝟙_ _) {i : ℤ} (x : 𝟙_ _ ⟶ C⟦i⟧) (y : S ⟶ D⟦-i⟧) :
    S ⟶ 𝟙_ _ :=
  (derivedTensorLeftUnitor A Y S).inv ≫ ((derivedTensor A Y).map x).app S ≫
    ((derivedTensor A Y).obj (C⟦i⟧)).map y ≫ (derivedTensorShiftIso A C D i (-i)).hom ≫
      (shiftFunctorZero' _ (i + -i) (add_neg_cancel i)).hom.app _ ≫ β

lemma degreeZeroPairingOfPairingAux_add_left {C D S : 𝐃(Y, A)}
    (β : ((derivedTensor A Y).obj C).obj D ⟶ 𝟙_ _) {i : ℤ} (x x' : 𝟙_ _ ⟶ C⟦i⟧) (y : S ⟶ D⟦-i⟧) :
    degreeZeroPairingOfPairingAux β (x + x') y =
      degreeZeroPairingOfPairingAux β x y + degreeZeroPairingOfPairingAux β x' y := by
  simp [degreeZeroPairingOfPairingAux, derivedTensor]

lemma degreeZeroPairingOfPairingAux_add_right {C D S : 𝐃(Y, A)}
    (β : ((derivedTensor A Y).obj C).obj D ⟶ 𝟙_ _) {i : ℤ} (x : 𝟙_ _ ⟶ C⟦i⟧) (y y' : S ⟶ D⟦-i⟧) :
    degreeZeroPairingOfPairingAux β x (y + y') =
      degreeZeroPairingOfPairingAux β x y + degreeZeroPairingOfPairingAux β x y' := by
  simp [degreeZeroPairingOfPairingAux, derivedTensor, MonoidalPreadditive.whiskerLeft_add]

/-- The degree-zero part of a pairing `β : C ⊗ᴸ D ⟶ Λ_Y` in degree `i`, as a biadditive map
`Hom(Λ_Y, C[i]) × Hom(S, D[-i]) ⟶ Hom(S, Λ_Y)`
(`AlgebraicGeometry.Etale.degreeZeroPairingOfPairingAux`). -/
noncomputable def degreeZeroPairingOfPairing {C D : 𝐃(Y, A)}
    (β : ((derivedTensor A Y).obj C).obj D ⟶ 𝟙_ _) (i : ℤ) (S : 𝐃(Y, A)) :
    ((𝟙_ 𝐃(Y, A)) ⟶ C⟦i⟧) →+ (S ⟶ D⟦-i⟧) →+ (S ⟶ 𝟙_ 𝐃(Y, A)) :=
  AddMonoidHom.mk'
    (fun x ↦ AddMonoidHom.mk' (degreeZeroPairingOfPairingAux β x)
      (degreeZeroPairingOfPairingAux_add_right β x))
    fun x x' ↦ by
      ext y
      exact degreeZeroPairingOfPairingAux_add_left β x x' y

end General

namespace TateOrientation

variable {Λ : Type (u + 1)} [CommRing Λ] [Finite Λ] [HasTateTwist Λ] {X Y : Scheme.{u}}
  {a : X ⟶ Y} [HasCompactification a] {d : ℕ}
  [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y]

/-- Blueprint `corollary-degreewise-duality-over-fields--1`: Degree of the pairing.

The degree-zero part of the derived Poincaré pairing `β_K` of a Tate orientation `γ`
(`AlgebraicGeometry.Etale.TateOrientation.poincarePairing`): the biadditive pairing of
`Hⁱ_c(X, K)` with `H⁻ⁱ(RΓ(X, K^∨(d))[2d])` with values in `Hom(Λ_Y, Λ_Y) = Λ`. -/
noncomputable def degreeZeroPairing (γ : TateOrientation Λ a d) (K : DerivedCategoryModule Λ X)
    (i : ℤ) :
    ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧) →+
      ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶
        (((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦(2 * d : ℤ)⟧)⟦-i⟧) →+
      ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ 𝟙_ (DerivedCategoryModule Λ Y)) :=
  degreeZeroPairingOfPairing (γ.poincarePairing K) i _

/-- Blueprint `corollary-degreewise-duality-over-fields--1`: Degree of the pairing.

The degreewise Poincaré pairings `⟨-, -⟩ᵢ : Hⁱ_c(X, K) × Hʲ(X, K^∨(d)) ⟶ Λ`, `i + j = 2d`: the
degree-zero part of the derived Poincaré pairing
(`AlgebraicGeometry.Etale.TateOrientation.degreeZeroPairing`), with a class of
`Hʲ(X, K^∨(d))` read in `H⁻ⁱ(RΓ(X, K^∨(d))[2d])` through `M[j] ≅ M[2d][-i]`. -/
noncomputable def degreewisePairing (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d) :
    ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧) →+
      ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶
        ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦j⟧) →+
      ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ 𝟙_ (DerivedCategoryModule Λ Y)) :=
  (γ.degreeZeroPairing K i).compl₂ (Preadditive.rightComp _
    ((shiftFunctorAdd' _ (2 * d : ℤ) (-i) j (by lia)).hom.app _))

omit [HasInvertibleExponent Λ X] [HasInvertibleExponent Λ Y] in
/-- Blueprint `corollary-degreewise-duality-over-fields--1`: Degree of the pairing.

The degreewise pairing `⟨x, y⟩ᵢ` is the degree-zero part of `β_K` evaluated on `x` and on the
class `y` read in degree `-i` of `RΓ(X, K^∨(d))[2d]`, by the shift convention
`H⁻ⁱ(M[2d]) = H^{2d-i}(M)`. -/
theorem degreewisePairing_apply (γ : TateOrientation Λ a d) (K : DerivedCategoryModule Λ X)
    (i j : ℤ) (hij : i + j = 2 * d)
    (x : (𝟙_ (DerivedCategoryModule Λ Y)) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧)
    (y : (𝟙_ (DerivedCategoryModule Λ Y)) ⟶
      ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦j⟧) :
    γ.degreewisePairing K i j hij x y = γ.degreeZeroPairing K i x
      (y ≫ (shiftFunctorAdd' _ (2 * d : ℤ) (-i) j (by lia)).hom.app _) :=
  rfl

/-- The *untwisting* of a class `y ∈ Hʲ(X, K^∨)`: the morphism `Λ_Y(d) ⟶ (Ra_*(K^∨(d)))[j]`
obtained by tensoring `y` with `Λ_Y(d)` and applying the projection map of `Ra_*` together with
`La^* Λ_Y(d) ≅ Λ_X(d)`:
```
            λ⁻¹                   y ⊗ 1                      ≅
Λ_Y(d) ──────▶ Λ_Y ⊗ᴸ Λ_Y(d) ─────────▶ (Ra_* K^∨)[j] ⊗ᴸ Λ_Y(d) ──▶ (Ra_* K^∨ ⊗ᴸ Λ_Y(d))[j]
       projection map                                    ≅
     ──────────────▶ (Ra_*(K^∨ ⊗ᴸ La^* Λ_Y(d)))[j] ─────────▶ (Ra_*(K^∨ ⊗ᴸ Λ_X(d)))[j]
```
This is the identification `Hʲ(X, K^∨(d)) ≅ Hʲ(X, K^∨) ⊗ Λ(d)`. -/
noncomputable def untwistClass (K : DerivedCategoryModule Λ X) (j : ℤ) :
    ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦j⟧) →+
      (tateObject Λ Y d ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj (twistedDual Λ d K))⟦j⟧) :=
  (Preadditive.rightComp _
    ((((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).commShiftIso j).hom.app _ ≫
      (((rightDerivedLowerStarProjectionMap _ a).app
        ((DerivedCategory.coefficientDual _ X).obj (op K))).app (tateObject Λ Y d))⟦j⟧' ≫
      ((R((a)_*[ModuleCat.{u + 1} Λ])).map (((derivedTensor _ X).obj _).map
        (leftDerivedUpperStarTateObjectIso a d).hom))⟦j⟧')).comp
    ((Preadditive.leftComp _ (derivedTensorLeftUnitor _ Y (tateObject Λ Y d)).inv).comp
      (((derivedTensor _ Y).flip.obj (tateObject Λ Y d)).mapAddHom))

/-- Blueprint `corollary-degreewise-duality-over-fields--1`: Degree of the pairing.

The line-valued Poincaré pairings `Hⁱ_c(X, K) × Hʲ(X, K^∨) ⟶ Λ(-d)`, `i + j = 2d`, obtained
from the same morphism `β_K` by eliminating the twist `Λ_X(d)` of the second factor: the
untwisting `y ↦ Λ_Y(d) ⟶ (Ra_*(K^∨(d)))[j]`
(`AlgebraicGeometry.Etale.TateOrientation.untwistClass`) is paired with `x` by the degree-zero
part of `β_K`, which gives a morphism `Λ_Y(d) ⟶ Λ_Y`, and this is tensored with the twist
inverse `Λ_Y(-d)` and read through `Λ_Y ≅ Λ_Y(d) ⊗ᴸ Λ_Y(-d)`. -/
noncomputable def untwistedDegreewisePairing (γ : TateOrientation Λ a d)
    (K : DerivedCategoryModule Λ X) (i j : ℤ) (hij : i + j = 2 * d) :
    ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)⟦i⟧) →+
      ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ ((R((a)_*[ModuleCat.{u + 1} Λ])).obj
        ((DerivedCategory.coefficientDual _ X).obj (op K)))⟦j⟧) →+
      ((𝟙_ (DerivedCategoryModule Λ Y)) ⟶ tateObject Λ Y (-d)) :=
  ((degreeZeroPairingOfPairing (γ.poincarePairing K) i (tateObject Λ Y d)).compl₂
    ((Preadditive.rightComp _ ((shiftFunctorAdd' _ (2 * d : ℤ) (-i) j (by lia)).hom.app _)).comp
      (untwistClass K j))).compr₂
    ((Preadditive.leftComp _ (constantComplexIsoTateObjectTensor Y d).hom).comp
      ((Preadditive.rightComp _ (derivedTensorLeftUnitor _ Y (tateObject Λ Y (-d))).hom).comp
        ((derivedTensor _ Y).flip.obj (tateObject Λ Y (-d))).mapAddHom))

end TateOrientation

section FieldDuality

variable (Λ : Type (u + 1)) [CommRing Λ] {k : Type u} [Field k] [IsSepClosed k]

/-- Over a separably closed field `k`, derived global sections carry a perfect pairing
`b : C ⊗ᴸ D ⟶ Λ` in `D(Spec k_ét, Λ)`, with `C ∈ D^b_c(Spec k, Λ)`, to a duality
`RΓ(Spec k, D) ≅ RΓ(Spec k, C)^∨` in `D(Λ)`: the pairing identifies `D` with the dual `C^∨`,
and evaluation at the point carries `C^∨` to `RΓ(Spec k, C)^∨`
(`AlgebraicGeometry.Etale.nonempty_iso_rightDerivedGlobalSections_coefficientDual`, blueprint
`theorem-global-verdier-duality`). -/
theorem nonempty_iso_rightDerivedGlobalSections_of_isPerfectPairing
    {C D : DerivedCategoryModule Λ (Spec (.of k))}
    (hC : DerivedCategory.boundedConstructible (ModuleCat.{u + 1} Λ) (Spec (.of k)) C)
    {b : ((derivedTensor (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C).obj D ⟶ 𝟙_ _}
    (hb : IsPerfectPairing b) :
    Nonempty ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj D ≅
      (ihom ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj C)).obj
        (𝟙_ _)) :=
  (nonempty_iso_rightDerivedGlobalSections_coefficientDual hC).map fun e ↦
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).mapIso hb.iso ≪≫ e

variable [IsDomain Λ] [Finite Λ] [HasTateTwist Λ] {X : Scheme.{u}} {a : X ⟶ Spec (.of k)}
  [HasCompactification a] [HasInvertibleExponent Λ X] {d : ℕ}

variable {Λ}

namespace TateOrientation

/-- Blueprint `corollary-degreewise-duality-over-fields`: Degreewise duality over a field
(finite-field case, non-canonical form). This is the finite-field, non-canonical form of blueprint
`corollary-degreewise-duality-over-fields--1`: only an abstract isomorphism, that is an equality
of dimensions, is proved, not that the adjoint of the degreewise pairing `⟨-, -⟩_i` is an
isomorphism (see the implementation notes of this file).

Let `k` be separably closed, `Λ` a finite field (a finite domain) whose characteristic is
invertible on `X`, `γ` a Tate orientation of `a : X ⟶ Spec k` of relative dimension `d`, with
`a` locally of finite type, and `K ∈ D^b_{ctf}(X, Λ)` perfect over `Λ_X`. Then for every `i` the
cohomology spaces `H^i_c(X, K)` and `H^{2d-i}(X, K^∨(d))` are finite-dimensional and

`H^{2d-i}(X, K^∨(d)) ≅ H^i_c(X, K)^∨`.

It follows from the derived duality `RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`
(`AlgebraicGeometry.Etale.TateOrientation.isPerfectPairing_poincarePairing`) by taking
`H^{-i}`, since over a field `H^{-i}(C^∨) ≅ H^i(C)^∨` for `C = RΓ_c(X, K)`
(`DerivedCategory.nonempty_iso_homology_ihom`). -/
theorem degreewise_duality [LocallyOfFiniteType a] (γ : TateOrientation Λ a d)
    {K : DerivedCategoryModule Λ X} (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K)
    (hKd : IsDualizable K) (i : ℤ) :
    Module.Finite Λ ((H_c(a)[ModuleCat.{u + 1} Λ](i)).obj K) ∧
      Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (2 * d - i)).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj (twistedDual Λ d K))) ∧
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (2 * d - i)).obj
          ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj (twistedDual Λ d K)) ≅
        ModuleCat.of Λ (Module.Dual Λ ((H_c(a)[ModuleCat.{u + 1} Λ](i)).obj K))) := by
  have hΛ : IsField Λ := Finite.isField_of_domain Λ
  let RΓ := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))
  let C := (R(a)_![ModuleCat.{u + 1} Λ]).obj K
  obtain ⟨eA⟩ := nonempty_iso_rightDerivedGlobalSections_of_isPerfectPairing Λ
    (boundedConstructible_rightDerivedLowerShriek Λ a a (𝟙 _) (Category.comp_id a) K hK.1)
    (γ.isPerfectPairing_poincarePairing hKd)
  obtain ⟨eB⟩ := DerivedCategory.nonempty_iso_homology_ihom hΛ (RΓ.obj C) i
  let e := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (2 * d - i)).mapIso
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ a).app _).symm ≪≫
    (((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0).shiftIso (2 * d : ℤ) (-i)
      (2 * d - i) (by ring)).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (-i)).mapIso
      ((RΓ.commShiftIso (2 * d : ℤ)).app _).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (-i)).mapIso eA ≪≫ eB
  have hfin : Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
      (RΓ.obj C)) := finite_compactlySupportedCohomology Λ a K hK i
  have : Module.Free Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
      (RΓ.obj C)) := by
    let _ := hΛ.toField
    exact Module.Free.of_divisionRing _ _
  exact ⟨hfin, Module.Finite.equiv e.toLinearEquiv.symm, ⟨e⟩⟩

/-- Blueprint `theorem-poincare-duality--8`: Proper Poincaré duality (degreewise form,
finite-field case, non-canonical form). As for
`AlgebraicGeometry.Etale.TateOrientation.degreewise_duality`, only an abstract isomorphism (an
equality of dimensions) is proved, not the perfectness of the degreewise pairing.

In the situation of `AlgebraicGeometry.Etale.TateOrientation.degreewise_duality`, if moreover
`a` is proper, then for every `i` the cohomology spaces `H^i(X, K)` and `H^{2d-i}(X, K^∨(d))`
are finite-dimensional and

`H^{2d-i}(X, K^∨(d)) ≅ H^i(X, K)^∨`,

since `RΓ_c(X, K) ≅ RΓ(X, K)` for proper `a`. -/
theorem degreewise_duality_of_isProper [IsProper a] (γ : TateOrientation Λ a d)
    {K : DerivedCategoryModule Λ X} (hK : DerivedCategory.boundedConstructibleFiniteTor Λ X K)
    (hKd : IsDualizable K) (i : ℤ) :
    Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K)) ∧
      Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (2 * d - i)).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj (twistedDual Λ d K))) ∧
      Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (2 * d - i)).obj
          ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj (twistedDual Λ d K)) ≅
        ModuleCat.of Λ (Module.Dual Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ)
          i).obj ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X).obj K)))) := by
  obtain ⟨hc, hfin, ⟨e⟩⟩ := γ.degreewise_duality hK hKd i
  let f := (DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).mapIso
    ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).mapIso
      ((rightDerivedLowerShriekIsoRightDerivedLowerStar _ a).app K) ≪≫
        (rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ a).app K)
  have : Module.Finite Λ ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
      ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
        ((R(a)_![ModuleCat.{u + 1} Λ]).obj K))) := hc
  exact ⟨Module.Finite.equiv f.toLinearEquiv, hfin,
    ⟨e ≪≫ f.toLinearEquiv.symm.dualMap.toModuleIso⟩⟩

end TateOrientation

end FieldDuality

end Etale

end AlgebraicGeometry
