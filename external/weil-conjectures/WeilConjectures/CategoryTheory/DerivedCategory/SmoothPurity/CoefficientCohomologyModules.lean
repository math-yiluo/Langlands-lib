/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFiniteCohomologyComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFgCompleteComplexes
public import WeilConjectures.CategoryTheory.DerivedCategory.Point.PointFdQbarCategory
public import WeilConjectures.CategoryTheory.DerivedCategory.Field.FieldDerivedScalarTower
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import WeilConjectures.Compactification.FiniteFieldDatum.FiniteFieldFiberSupplement

/-! # Cohomology modules of coefficient complexes

Source: Weil blueprint, `def-weil-ordinary-compact-cohomology`, order 1510,
with the four coefficient categories of `lemma-perfect-complexes-geometric-point`, order 1509
(blueprint: def-weil-coefficient-cohomology-modules).

The generic ring-level functor is Mathlib's `DerivedCategory.homologyFunctor`.
Its value on a representing complex is ker(d)/im(d), by
`DerivedCategory.homologyFunctorFactors` and `ShortComplex.moduleCatHomologyIso`.
The first three functors below are its restrictions to the prescribed full subcategories.
For the global datum D and coefficient datum c, specialize their rings to
`Padic.coefficientExtensionRing c.l E n`, `Padic.coefficientExtensionIntegers c.l E`,
and E, respectively; the integral ideal is `Padic.coefficientExtensionIdeal c.l E 1`.
The finite-stage Qbar functor has literally the scalar-extended cohomology as object data.

## Main definitions

* `coefficientCohomologyModules`: the four functors for the fixed global coefficient datum.
* `coefficientQbarCohomology`: literal scalar-extended cohomology on a finite-stage pair.
* `coefficientCohomologyChangeStage`: the canonical identification after enlarging the stage.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace DerivedCategory

/-- Cohomology restricted to bounded finite-dimensional coefficient complexes.
Source: blueprint order 1510 (blueprint: def-weil-coefficient-cohomology-modules). -/
noncomputable def coefficientFdCohomology (F : Type u) [Field F] (i : ℤ) :
    (pointFiniteDimensional F).FullSubcategory ⥤ ModuleCat.{u} F :=
  (pointFiniteDimensional F).ι ⋙ homologyFunctor (ModuleCat.{u} F) i

variable (l : ℕ) [Fact l.Prime] (Ω : Type u) [Field Ω] [Algebra (Padic l) Ω]
  [IsAlgClosure (Padic l) Ω]

end DerivedCategory
