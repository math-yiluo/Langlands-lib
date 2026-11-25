/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Perfect complexes on schemes

Source: literature/blueprint/master/blueprint/sec-picard-framework/det-thm-picard-semicon/
def-pc-perfect-complex.md, node lemma-coherent-base-change-invertible-sheaves--1, order 664; Stacks
Project, Cohomology of Sheaves, Definitions 08C4 and 08CM, Tag 0BDH (blueprint:
lemma-coherent-base-change-invertible-sheaves--1).

Restriction to an open is `SheafOfModules.overFunctor` on the localized site, with the same
module category and derived category as `schemeDerivedCategory`, in the shape of
`AlgebraicGeometry.Scheme.IsPseudoCoherent` (blueprint: def-pur-pseudo-coherent-complex).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A complex of `𝒪_U`-modules on an open `U` of `X` is strictly perfect if all but finitely
many of its terms are zero and each term is a direct summand of a finite free `𝒪_U`-module:
there are `ι : K.X n ⟶ 𝒪_U^m` and `π : 𝒪_U^m ⟶ K.X n` with `ι ≫ π = 𝟙 (K.X n)`.
Source: Stacks Project, Cohomology of Sheaves, Definition 08C4
(blueprint: lemma-coherent-base-change-invertible-sheaves--1). -/
def IsStrictlyPerfect (X : Scheme.{u}) (U : X.Opens)
    (K : CochainComplex (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ) :
    Prop :=
  (∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (K.X n)) ∧
    ∀ n : ℤ, ∃ m : ℕ,
      ∃ (ι : K.X n ⟶ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)))
        (π : SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin m)) ⟶ K.X n),
        ι ≫ π = 𝟙 (K.X n)

/-- An object `E` of `D(𝒪_X)` is perfect if every point has an open neighbourhood `U` (that
is, there is an open covering of `X`) on which the restriction of `E` is isomorphic in
`D(𝒪_U)` to a strictly perfect complex of `𝒪_U`-modules. Along
`AlgebraicGeometry.schemeDerivedCategoryEquiv X` this is
`AlgebraicGeometry.Scheme.Modules.IsPerfectComplex`
(`AlgebraicGeometry.Scheme.isPerfect_iff_isPerfectComplex`).
Source: Stacks Project, Cohomology of Sheaves, Definition 08CM
(blueprint: lemma-coherent-base-change-invertible-sheaves--1). -/
def IsPerfect (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) : Prop :=
  ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
    ∃ K : CochainComplex
        (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
      IsStrictlyPerfect X U K ∧
      Nonempty ((SheafOfModules.overFunctor.{u}
        (moduleRings X.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj K)

/-- The full subcategory `D_perf(𝒪_X)` of `D(𝒪_X)` of perfect objects.
Source: Stacks Project, Cohomology of Sheaves, Definition 08CM
(blueprint: lemma-coherent-base-change-invertible-sheaves--1). -/
def perfectSubcategory (X : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))] :
    ObjectProperty (schemeDerivedCategory X) :=
  IsPerfect X

end AlgebraicGeometry.Scheme
