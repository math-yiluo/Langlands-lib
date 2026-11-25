/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.AlgebraicGeometry.AffineSpace
public import WeilConjectures.AlgebraicGeometry.InvertibleExponent
public import WeilConjectures.EtaleCohomology.Purity.Smooth.Conventions
public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import WeilConjectures.Mathlib.AlgebraicGeometry.Restrict
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriekToLowerStar
public import WeilConjectures.SixFunctors.Etale.Derived.Supports

/-!
# Kummer classes and their boundaries

The cohomological constructions out of which the fundamental class of a regular closed
immersion is glued (`lemma-class-of-point--1`):

* the *Kummer class* `κ(u) ∈ H¹(X, Λ(1))` of a unit `u`, the rank-one datum of
  `sk-def-purity-conv`, supplied by `AlgebraicGeometry.Etale.HasKummerClass`;
* the *Kummer boundary* `∂κ(f) ∈ H²_{V(f)}(U, Λ(1))` of a global function `f`: `f` is a unit
  on the open complement `U ∖ V(f)`, and the boundary of the supported localization triangle
  of `V(f) ⊂ U` carries its Kummer class to a class supported on `V(f)`;
* the iterated cup product with supports `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_n)`, supported on `V(f₁, …, f_n)`.

A class with supports in `Z`, of degree `n` and coefficients `L`, is a morphism
`Λ_U ⟶ (Ri_! Ri^! L)[n]`, where `i : Z ⟶ U` is the closed immersion; the operations on such
classes are those of `WeilConjectures.SixFunctors.Etale.Derived.Supports`.

## Implementation notes

Like the Tate twist, the Kummer classes are taken as a parameter, the class
`AlgebraicGeometry.Etale.HasKummerClass`. Naturality and multiplicativity alone do not pin it
down (`κ = 0` satisfies both), so the statements that depend on the actual classes also assume
the *rank-one normalisation* `AlgebraicGeometry.Etale.HasKummerClass.IsNormalized`: the boundary
`∂κ(t)` of the coordinate of `𝔸¹_B` is the fundamental class of the zero section, in the sense
that its adjoint `Λ_B ⟶ Rs^! (Λ(1)[2])` is an isomorphism. This is the rank-one local calculation
of the blueprint, and it also pins down the twisting object `Λ(1)`.

## Main definitions

- `AlgebraicGeometry.Etale.HasKummerClass`: the rank-one datum.
- `AlgebraicGeometry.Etale.kummerClass`: `κ(u) ∈ H¹(X, Λ(1))`.
- `AlgebraicGeometry.Etale.kummerBoundary`: `∂κ(f) ∈ H²_{V(f)}(U, Λ(1))`.
- `AlgebraicGeometry.Etale.supportedClassMap`: the adjoint `Λ_Z ⟶ Ri^! L` of a class with
  supports.
- `AlgebraicGeometry.Etale.HasKummerClass.IsNormalized`: the rank-one normalisation.
- `AlgebraicGeometry.Etale.HasTateTwist.IsNormalized`: a twist datum underlying a normalized
  rank-one datum, the hypothesis of every statement comparing the twist with geometry.
- `AlgebraicGeometry.Etale.cupWithSupportsTateObject`: the cup product of classes with supports
  and Tate coefficients.
- `AlgebraicGeometry.Etale.kummerBoundaryProduct`: `∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_n)`.

## Main statements

- `AlgebraicGeometry.Etale.leftDerivedUpperStar_map_kummerClass`,
  `AlgebraicGeometry.Etale.kummerClass_mul`
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

/-- The characteristic of `Λ` is invertible on relative affine space over a scheme on which it
is invertible. -/
instance hasInvertibleExponent_affineSpace {Λ : Type (u + 1)} [CommRing Λ] {n : Type u}
    {B : Scheme.{u}} [HasInvertibleExponent Λ B] : HasInvertibleExponent Λ 𝔸(n; B) :=
  .of_hom (𝔸(n; B) ↘ B)

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- Blueprint `sk-def-purity-conv`: Purity conventions and the rank-one datum

The *rank-one datum*: on top of a Tate twist datum, the *Kummer class*
`κ(u) ∈ H¹(X, Λ(1)) = Hom(Λ_X, Λ_X(1)[1])` of every unit `u ∈ Γ(X, 𝒪_X)ˣ`, natural under
pullback and multiplicative in `u`.

**The concrete model.** With `Λ_X(1) = μ_{ℓ^N} ⊗ Λ` and `ℓ^N Λ = 0`, `κ(u)` is the image of `u`
under the boundary `Γ(X, 𝔾_m) ⟶ H¹(X, μ_{ℓ^N})` of the Kummer sequence
`0 → μ_{ℓ^N} → 𝔾_m → 𝔾_m → 0` (`AlgebraicGeometry.Scheme.kummerSequence` with `n = ℓ^N`),
tensored with `Λ`. Equivalently `κ(u)` is the class of the `μ_{ℓ^N}`-torsor
`Spec 𝒪_X[T]/(T^{ℓ^N} − u)`. For `u = t` the coordinate of `𝔾_{m,Y}` this is the class `κ(t)` of
`sk-def-purity-conv`. -/
class HasKummerClass extends HasTateTwist Λ where
  /-- The *Kummer class* `κ(u) ∈ H¹(X, Λ(1)) = Hom(Λ_X, Λ_X(1)[1])` of a unit
  `u ∈ Γ(X, 𝒪_X)ˣ`. -/
  kummerClass (X : Scheme.{u}) [HasInvertibleExponent Λ X] (u : Γ(X, ⊤)ˣ) :
    constantComplex Λ X ⟶ (twistObject X 1)⟦(1 : ℤ)⟧
  /-- The Kummer class is natural under pullback, `Lf^* κ(u) = κ(f^* u)`, along the
  identifications `Lf^* Λ_Y ≅ Λ_X` and `Lf^* Λ_Y(1) ≅ Λ_X(1)` of the twist datum:

  ```
  Lf^* Λ_Y ──Lf^* κ(u)──▶ Lf^*(Λ_Y(1)[1]) ≅ (Lf^* Λ_Y(1))[1]
     │ ≅                              │ ≅
     ▼                                ▼
    Λ_X ───────κ(f^* u)──────────▶ Λ_X(1)[1]
  ``` -/
  leftDerivedUpperStar_map_kummerClass {X Y : Scheme.{u}} [HasInvertibleExponent Λ X]
      [HasInvertibleExponent Λ Y] (f : X ⟶ Y) (u : Γ(Y, ⊤)ˣ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (kummerClass Y u) ≫
        ((L((f)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app (twistObject Y 1) ≫
          (leftDerivedUpperStarTwistObjectIso f 1).hom⟦(1 : ℤ)⟧' =
      (leftDerivedUpperStarConstantComplexIso Λ f).hom ≫
        kummerClass X (Units.map f.appTop.hom.toMonoidHom u)
  /-- The Kummer class is multiplicative, `κ(uv) = κ(u) + κ(v)`: the Kummer boundary is a
  group homomorphism. -/
  kummerClass_mul (X : Scheme.{u}) [HasInvertibleExponent Λ X] (u v : Γ(X, ⊤)ˣ) :
    kummerClass X (u * v) = kummerClass X u + kummerClass X v

variable [HasKummerClass Λ]

section Kummer

variable {X Y : Scheme.{u}}

/-- Blueprint `sk-def-purity-conv`: Purity conventions and the rank-one datum

The *Kummer class* `κ(u) ∈ H¹(X, Λ(1)) = Hom(Λ_X, Λ_X(1)[1])` of a unit `u ∈ Γ(X, 𝒪_X)ˣ`,
from the rank-one datum `AlgebraicGeometry.Etale.HasKummerClass`. In the concrete model,
`Λ(1) = μ_{ℓ^N} ⊗ Λ` with `ℓ^N Λ = 0`, it is the boundary of `u` in the Kummer sequence
`0 → μ_{ℓ^N} → 𝔾_m → 𝔾_m → 0` (`AlgebraicGeometry.Scheme.kummerSequence`), tensored with `Λ`;
for the coordinate `t` of `𝔾_{m,Y}` it is the class `κ(t)` of `sk-def-purity-conv`. -/
noncomputable def kummerClass [HasInvertibleExponent Λ X] (u : Γ(X, ⊤)ˣ) :
    constantComplex Λ X ⟶ (tateObject Λ X 1)⟦(1 : ℤ)⟧ :=
  HasKummerClass.kummerClass X u

/-- The Kummer class is natural under pullback: `Lf^* κ(u) = κ(f^* u)`, along the
identifications `Lf^* Λ_Y ≅ Λ_X` and `Lf^* Λ_Y(1) ≅ Λ_X(1)`:

```
Lf^* Λ_Y ──Lf^* κ(u)──▶ Lf^*(Λ_Y(1)[1]) ≅ (Lf^* Λ_Y(1))[1]
   │ ≅                              │ ≅
   ▼                                ▼
  Λ_X ───────κ(f^* u)──────────▶ Λ_X(1)[1]
``` -/
theorem leftDerivedUpperStar_map_kummerClass [HasInvertibleExponent Λ X]
    [HasInvertibleExponent Λ Y] (f : X ⟶ Y) (u : Γ(Y, ⊤)ˣ) :
    (L((f)^*[ModuleCat.{u + 1} Λ])).map (kummerClass Λ u) ≫
        ((L((f)^*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app (tateObject Λ Y 1) ≫
          (leftDerivedUpperStarTateObjectIso f 1).hom⟦(1 : ℤ)⟧' =
      (leftDerivedUpperStarConstantComplexIso Λ f).hom ≫
        kummerClass Λ (Units.map f.appTop.hom.toMonoidHom u) :=
  HasKummerClass.leftDerivedUpperStar_map_kummerClass f u

/-- The Kummer class is multiplicative: `κ(uv) = κ(u) + κ(v)`. -/
theorem kummerClass_mul [HasInvertibleExponent Λ X] (u v : Γ(X, ⊤)ˣ) :
    kummerClass Λ (u * v) = kummerClass Λ u + kummerClass Λ v :=
  HasKummerClass.kummerClass_mul X u v

end Kummer

section Boundary

variable [Finite Λ]

variable {U : Scheme.{u}} [HasInvertibleExponent Λ U] (f : Γ(U, ⊤))

/-- The *Kummer boundary* `∂κ(f) ∈ H²_{V(f)}(U, Λ(1))` of a global function `f` on `U`. Write
`i : V(f) ⟶ U` for the closed subscheme cut out by `f` and `j : U_f ⟶ U` for its open
complement, on which `f` is a unit. The Kummer class `κ(f|_{U_f}) ∈ H¹(U_f, Λ(1))`, read through
`Lj^* Λ_U ≅ Λ_{U_f}` and `Lj^* Λ_U(1) ≅ Λ_{U_f}(1)`, is adjoint under `Lj^* ⊣ Rj_*` to a class
`Λ_U ⟶ (Rj_* Lj^* Λ_U(1))[1]`, and the boundary
`δ : Rj_* Lj^* Λ_U(1) ⟶ (Ri_! Ri^! Λ_U(1))[1]` of the supported localization triangle
(`AlgebraicGeometry.Etale.supportedLocalizationBoundary`) carries it to

`∂κ(f) : Λ_U ⟶ (Ri_! Ri^! Λ_U(1))[2]`.

The supported term is `Ri_!`, as in the supported localization triangle; for the closed
immersion `i` it is `Ri_*`. -/
noncomputable def kummerBoundary :
    constantComplex Λ U ⟶
      ((R(U.zeroLocusSubschemeι {f})_![ModuleCat.{u + 1} Λ]).obj
        ((R(U.zeroLocusSubschemeι {f})^![Λ]).obj (tateObject Λ U 1)))⟦(2 : ℤ)⟧ :=
  haveI : HasInvertibleExponent Λ (U.basicOpen f) := .of_hom (U.basicOpen f).ι
  ((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) (U.basicOpen f).ι).homEquiv _ _
      ((leftDerivedUpperStarConstantComplexIso Λ (U.basicOpen f).ι).hom ≫
        kummerClass Λ (U.basicOpenUnit f) ≫
          (leftDerivedUpperStarTateObjectIso (U.basicOpen f).ι 1).inv⟦(1 : ℤ)⟧')) ≫
    ((R(((U.basicOpen f).ι)_*[ModuleCat.{u + 1} Λ])).commShiftIso (1 : ℤ)).hom.app _ ≫
      (supportedLocalizationBoundary Λ _ _
        (range_zeroLocusSubschemeι_singleton f) (tateObject Λ U 1))⟦(1 : ℤ)⟧' ≫
        (shiftFunctorAdd' _ (1 : ℤ) 1 2 rfl).inv.app _

end Boundary

section Normalization

variable [Finite Λ]

variable {X Z : Scheme.{u}}

/-- The *adjoint* `Λ_Z ⟶ Ri^! L` of a class `γ : Λ_X ⟶ Ri_! Ri^! L` supported on the closed
immersion `i : Z ⟶ X`: the transpose of `γ` along the forget-supports map `Ri_! ⟶ Ri_*`
(`AlgebraicGeometry.Etale.rightDerivedLowerShriekTranspose`), read through `Li^* Λ_X ≅ Λ_Z`.
For `γ` the fundamental class of `Z` it is the map `cl_i`, `1 ↦ [Z ⊂ X]`. -/
noncomputable def supportedClassMap (i : Z ⟶ X) [IsClosedImmersion i]
    {L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))}
    (γ : constantComplex Λ X ⟶
      (R(i)_![ModuleCat.{u + 1} Λ]).obj ((R(i)^![Λ]).obj L)) :
    constantComplex Λ Z ⟶ (R(i)^![Λ]).obj L :=
  (compactificationConstantComplexIso Λ i).inv ≫
    rightDerivedLowerShriekTranspose (ModuleCat.{u + 1} Λ) i γ

omit [HasKummerClass Λ] in
/-- Blueprint `sk-prop-a1`: Rank-one orientation: the fundamental class of the zero section

*Classes with supports are morphisms out of the constant complex of the support.* For a closed
immersion `i : Z ⟶ X` and `L ∈ D(X_ét, Λ)`, the adjoint `γ ↦ (Λ_Z ⟶ Ri^! L)`
(`AlgebraicGeometry.Etale.supportedClassMap`) is a bijection

`H_Z(X, L) = Hom(Λ_X, Ri_! Ri^! L) ≅ Hom(Λ_Z, Ri^! L)`.

For the zero section of the affine line and `L = Λ(1)[2]` this is the identification of the
global sections `Hom(Λ_Y, Rs^! Λ(1)[2])` with the module `H²_{s(Y)}(𝔸¹_Y, Λ(1))`. The
forget-supports map `Ri_! ⟶ Ri_*` is invertible since `i` is proper, and `Li^* ⊣ Ri_*`. -/
theorem supportedClassMap_bijective (i : Z ⟶ X) [IsClosedImmersion i]
    (L : DerivedCategory (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    Function.Bijective (supportedClassMap Λ i (L := L)) := by
  let E := ((Iso.refl _).homCongr (asIso ((rightDerivedLowerShriekToLowerStarComp
      (ModuleCat.{u + 1} Λ) i).app ((R(i)^![Λ]).obj L)))).trans
    ((((derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) _).comp
      (derivedUpperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) _)).homEquiv _ _).symm.trans
        ((compactificationConstantComplexIso Λ i).homCongr (Iso.refl _)))
  convert E.bijective using 1
  ext γ
  simp [E, supportedClassMap, rightDerivedLowerShriekTranspose]

/-- Blueprint `sk-def-purity-conv`: Purity conventions and the rank-one datum

The *rank-one normalisation* of the Kummer classes. For every scheme `B` separated and locally
of finite type over a field, on which the exponent of `Λ` is invertible, let `t` be the
coordinate of `𝔸¹_B` and `s : V(t) ⟶ 𝔸¹_B` the zero section. The Kummer boundary
`∂κ(t) ∈ H²_{V(t)}(𝔸¹_B, Λ(1))` is the fundamental class of the zero section: its adjoint
`Λ_{V(t)} ⟶ Rs^! (Λ(1)[2])` is an isomorphism.

This is the rank-one local calculation `H²_{0}(𝔸¹_ȳ, Λ(1)) ≅ Λ`, `∂κ(t) ↦ 1`, of the blueprint,
a theorem for the concrete model. Naturality and multiplicativity alone do not imply it (the
zero class satisfies both), and it also pins down the twisting object `Λ(1)`: by purity
`Rs^! Λ ≅ Λ(-1)[-2]` for the true twist, so the isomorphism forces `Λ_B(1) ≅ μ_n ⊗ Λ`, whereas
the fields of `AlgebraicGeometry.Etale.HasTateTwist` alone also admit `Λ_B(1) = Λ_B` and
`Λ_B(1) = Λ_B[-2]`. Its twist-side form `AlgebraicGeometry.Etale.HasTateTwist.IsNormalized` is
what the statements comparing the twist with geometry assume.

The schemes `B` are those of the blueprint statement `sk-prop-a1` (separated of finite type over
the base field): the same normalisation over an arbitrary base on which the exponent is invertible
is relative purity for the zero section of `𝔸¹_B` over a general base, which is true (SGA 4 XVI)
but beyond the blueprint, and is not needed by the statements assuming the class. -/
class HasKummerClass.IsNormalized : Prop where
  /-- The adjoint of the Kummer boundary of the coordinate of `𝔸¹_B` is an isomorphism. -/
  isIso_supportedClassMap_kummerBoundary_coord {k : Type u} [Field k] (B : Scheme.{u})
      (aB : B ⟶ Spec (.of k)) [IsSeparated aB] [LocallyOfFiniteType aB]
      [HasInvertibleExponent Λ B] :
    IsIso (supportedClassMap Λ (𝔸(ULift.{u} (Fin 1); B).zeroLocusSubschemeι
        {AffineSpace.coord B (ULift.up 0)})
      (shiftSupportedClass Λ _ 2
        (kummerBoundary Λ (AffineSpace.coord B (ULift.up 0)))))

end Normalization

section BoundaryProduct

variable [Finite Λ]

variable (U : Scheme.{u}) in
/-- The diagonal `Λ_U ⟶ Λ_U ⊗ Λ_U` along which cohomology classes are multiplied: the inverse of
the identification `Λ_U ⊗ Λ_U ≅ Λ_U(0) ⊗ Λ_U(0) ≅ Λ_U(0) ≅ Λ_U` of the Tate twist datum. By the
unit law `HasTateTwist.twistObjectAddIso_zero_left` it is the inverse of the left unitor; it is
not written as such because the kernel cannot compare the unitor of the monoidal derived
category with the derived tensor product of étale sheaves in reasonable time. -/
noncomputable def constantComplexDiagonal [HasInvertibleExponent Λ U] :
    constantComplex Λ U ⟶
      ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj (constantComplex Λ U)).obj
        (constantComplex Λ U) :=
  (HasTateTwist.twistObjectZeroIso (Λ := Λ) U).inv ≫ eqToHom (by rw [add_zero]) ≫
    (HasTateTwist.twistObjectAddIso U 0 0).inv ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) U).map (HasTateTwist.twistObjectZeroIso U).hom).app _ ≫
        ((derivedTensor (ModuleCat.{u + 1} Λ) U).obj _).map (HasTateTwist.twistObjectZeroIso U).hom

variable {U Z₁ Z₂ Z : Scheme.{u}} [HasInvertibleExponent Λ U]

/-- The cup product with supports of classes `α ∈ H^{2m}_{Z₁}(U, Λ(m))` and
`β ∈ H^{2m'}_{Z₂}(U, Λ(m'))`, a class in `H^{2(m + m')}_{Z₁ ∩ Z₂}(U, Λ(m + m'))`: the cup
product `AlgebraicGeometry.Etale.cupWithSupports` along the diagonal `Λ_U ≅ Λ_U ⊗ Λ_U`
(`AlgebraicGeometry.Etale.constantComplexDiagonal`), followed by
`Λ(m)[2m] ⊗ Λ(m')[2m'] ≅ Λ(m + m')[2(m + m')]` (`AlgebraicGeometry.Etale.shiftTateObjectAddIso`).
-/
noncomputable def cupWithSupportsTateObject (i₁ : Z₁ ⟶ U) (i₂ : Z₂ ⟶ U) (i : Z ⟶ U)
    [IsClosedImmersion i₁] [IsClosedImmersion i₂] [IsClosedImmersion i]
    (h : Set.range i.base = Set.range i₁.base ∩ Set.range i₂.base) {m m' : ℤ}
    (α : constantComplex Λ U ⟶ (R(i₁)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₁)^![Λ]).obj ((tateObject Λ U m)⟦2 * m⟧)))
    (β : constantComplex Λ U ⟶ (R(i₂)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i₂)^![Λ]).obj ((tateObject Λ U m')⟦2 * m'⟧))) :
    constantComplex Λ U ⟶ (R(i)_![ModuleCat.{u + 1} Λ]).obj
      ((R(i)^![Λ]).obj ((tateObject Λ U (m + m'))⟦2 * (m + m')⟧)) :=
  cupWithSupports Λ i₁ i₂ i h (constantComplexDiagonal Λ U) α β ≫
    (R(i)_![ModuleCat.{u + 1} Λ]).map ((R(i)^![Λ]).map
      (shiftTateObjectAddIso Λ U m m').hom)

/-- The *iterated cup product of Kummer boundaries* of a tuple `f = (f₁, …, f_n)` of global
functions on `U`:

`∂κ(f₁) ∪ ⋯ ∪ ∂κ(f_n) ∈ H^{2n}_{V(f)}(U, Λ(n)) = Hom(Λ_U, Ri_! Ri^! (Λ_U(n)[2n]))`,

where `i : V(f) ⟶ U` is the closed subscheme cut out by `f₁, …, f_n`. It is built by recursion
on `n`: the empty product is the unit class `Λ_U ≅ Λ_U(0)` supported everywhere
(`AlgebraicGeometry.Etale.liftCounitOfRangeEqUniv`), and
`∂κ(f₁) ∪ (∂κ(f₂) ∪ ⋯ ∪ ∂κ(f_n))` is the cup product with supports
(`AlgebraicGeometry.Etale.cupWithSupportsTateObject`) over `V(f₁) ∩ V(f₂, …, f_n) = V(f)`. All
the classes have even degree, so no sign is involved. -/
noncomputable def kummerBoundaryProduct : {n : ℕ} → (f : Fin n → Γ(U, ⊤)) →
    constantComplex Λ U ⟶
      (R(U.zeroLocusSubschemeι (Set.range f))_![ModuleCat.{u + 1} Λ]).obj
        ((R(U.zeroLocusSubschemeι (Set.range f))^![Λ]).obj
          ((tateObject Λ U n)⟦2 * (n : ℤ)⟧))
  | 0, f => liftCounitOfRangeEqUniv Λ _
      (by rw [Set.range_eq_empty f, range_zeroLocusSubschemeι_empty])
      ((HasTateTwist.twistObjectZeroIso (Λ := Λ) U).inv ≫
        (shiftFunctorZero' _ (2 * (0 : ℤ)) (by simp)).inv.app _)
  | n + 1, f =>
      cupWithSupportsTateObject Λ (U.zeroLocusSubschemeι {f 0})
          (U.zeroLocusSubschemeι (Set.range (Fin.tail f))) (U.zeroLocusSubschemeι (Set.range f))
          (by rw [Fin.range_fin_succ, range_zeroLocusSubschemeι_insert]) (m := 1)
          (shiftSupportedClass Λ _ 2 (kummerBoundary Λ (f 0)))
          (kummerBoundaryProduct (Fin.tail f)) ≫
        eqToHom (by rw [Nat.cast_succ, add_comm (1 : ℤ)])

end BoundaryProduct

end Etale

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ]

/-- Blueprint `sk-def-purity-conv`: Purity conventions and the rank-one datum

A Tate twist datum is *normalized* if it underlies a normalized rank-one datum: Kummer classes on
it whose boundary for the coordinate of `𝔸¹_B` is the fundamental class of the zero section
(`AlgebraicGeometry.Etale.HasKummerClass.IsNormalized`). This pins down the twist: it forces
`Λ_B(1) ≅ μ_n ⊗ Λ`, and hence `Λ_B(m) ≅ Λ_B(1)^{⊗ m}`, on every scheme `B` on which the exponent
`n` of `Λ` is invertible, whereas the fields of `AlgebraicGeometry.Etale.HasTateTwist` alone also
admit the untwisted datum `Λ_B(m) = Λ_B` and the shifted datum `Λ_B(m) = Λ_B[-2m]`.

The statements that compare the twist with geometry — `Rs^! Λ(1)[2] ≅ Λ` for the zero section of
the affine line, affine-space and smooth purity, purity for regular immersions, Fourier
inversion — assume it; they are false for the two data above. -/
class HasTateTwist.IsNormalized [inst : HasTateTwist Λ] : Prop where
  /-- The twist datum underlies a normalized rank-one datum. -/
  exists_hasKummerClass :
    ∃ K : HasKummerClass Λ, K.toHasTateTwist = inst ∧ @HasKummerClass.IsNormalized Λ _ K _

/-- The twist datum underlying a normalized rank-one datum is normalized. -/
instance HasKummerClass.IsNormalized.hasTateTwistIsNormalized [HasKummerClass Λ]
    [HasKummerClass.IsNormalized Λ] : HasTateTwist.IsNormalized Λ :=
  ⟨⟨‹_›, rfl, ‹_›⟩⟩

end Etale

end AlgebraicGeometry
