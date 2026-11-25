/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free

/-! # Pseudo-coherent complexes on schemes

Source: Stacks Project, Cohomology of Sheaves, Tag 08CB, and Derived Categories of Schemes,
Tags 08E5 and 08E7 (blueprint: def-pur-pseudo-coherent-complex).

We use the scheme-local characterization by bounded-above complexes of finite free modules.
Restriction is to the localized site of an open, using the same module category and derived
category as `schemeDerivedCategory`.
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- An object of `D(𝒪_Y)` is pseudo-coherent if every point has an open neighbourhood on
which it is isomorphic in the derived category to a bounded-above complex of finite free
modules. The upper bound and the finite ranks may depend on the neighbourhood; each rank
may depend on the degree. This is the scheme-local characterization of Stacks Project,
Tag 08CB, via Tags 08E5 and 08E7 (blueprint: def-pur-pseudo-coherent-complex). -/
def IsPseudoCoherent (Y : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ U : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))]
    (E : schemeDerivedCategory Y) : Prop :=
  ∀ y : Y, ∃ U : Y.Opens, y ∈ U ∧
    ∃ P : CochainComplex
        (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U)) ℤ,
      (∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
        (R := (moduleRings Y.toRingedSpace).over U) (ULift.{u} (Fin r)))) ∧
      Nonempty ((SheafOfModules.overFunctor.{u}
        (moduleRings Y.toRingedSpace) U).mapDerivedCategory.obj E ≅ DerivedCategory.Q.obj P)

end AlgebraicGeometry.Scheme
