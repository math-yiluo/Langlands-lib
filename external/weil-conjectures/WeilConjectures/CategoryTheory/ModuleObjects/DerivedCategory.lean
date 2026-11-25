/-
Copyright (c) 2026 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan
-/
module

public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory
public import WeilConjectures.CategoryTheory.Monoidal.Instances.CochainComplex
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategory
public import WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian

/-!

# The derived category of module objects and the derived tensor product

Let `C` be a closed symmetric monoidal Grothendieck abelian category whose tensor product is
additive, and let `R : C` be a commutative algebra object. Since `C` is closed, tensoring on
either side preserves colimits, so the category `Mod C R` of `R`-module objects is abelian
(`WeilConjectures.CategoryTheory.ModuleObjects.Abelian`) and symmetric monoidal for the relative
tensor product `⊗_R` (`WeilConjectures.CategoryTheory.ModuleObjects.Symmetric`). Hence it has an
ordinary derived category
```
D(Mod_R(C)) = DerivedCategory (Mod C R),
```
obtained by inverting the quasi-isomorphisms of complexes of `R`-modules. The tensor product of
complexes of `R`-modules is the totalization of the termwise relative tensor product, and the
*derived tensor product* `K ⊗ᴸ_R L` is computed by replacing `K` by a K-flat resolution. This is
the K-flat machinery of `WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`,
which makes `DerivedCategory (Mod C R)` a monoidal category with tensor product `⊗ᴸ_R`
(`Mod.derivedMonoidalCategory`), such that the localization functor from complexes of
`R`-modules is lax monoidal.

## Sorried input

The K-flat machinery requires three properties of `Mod C R`, inherited from `C`:
`Mod.monoidalClosed`, `Mod.isGrothendieckAbelian` and `Mod.hasFunctorialFlatResolution`. They
are currently `sorry`ed in `WeilConjectures.CategoryTheory.ModuleObjects.GrothendieckAbelian`.

The construction moreover uses the instance `DerivedCategory.hasDerivedMonoidalCategory`, which
is currently `sorry`ed in
`WeilConjectures.CategoryTheory.DerivedCategory.HasMonoidalDerivedCategory`.

-/

@[expose] public section

universe v u

open CategoryTheory MonoidalCategory Limits

namespace CategoryTheory.Mod

variable {C : Type u} [Category.{v} C] [Abelian C] [MonoidalCategory C] [MonoidalPreadditive C]
  [SymmetricCategory C] [MonoidalClosed C] {R : C} [MonObj R] [IsCommMonObj R]

variable [IsGrothendieckAbelian.{v} C] [Abelian.HasFunctorialFlatResolution C]
/-- Small colimits of module objects, from the Grothendieck abelian structure. -/
instance hasColimitsOfSize : HasColimitsOfSize.{0, 0} (Mod C R) :=
  hasColimitsOfSizeShrink _

/-- Complexes of module objects are monoidal for the total relative tensor product. -/
noncomputable instance monoidalCategoryCochainComplex :
    MonoidalCategory (CochainComplex (Mod C R) ℤ) :=
  inferInstance

/-- The derived category of module objects is monoidal for the derived tensor product
`K ⊗ᴸ_R L`. -/
noncomputable instance derivedMonoidalCategory :
    MonoidalCategory (DerivedCategory (Mod C R)) :=
  inferInstance

/-- The localization functor to the derived category of module objects is lax monoidal: the
derived tensor product receives a natural map from the tensor product of complexes. -/
noncomputable instance laxMonoidalQ : (DerivedCategory.Q (C := Mod C R)).LaxMonoidal :=
  inferInstance

/-- The derived tensor product of module objects is the left derived functor of the tensor
product of complexes with respect to quasi-isomorphisms: it is computed on K-flat
resolutions. -/
instance isLeftDerivedFunctor₂_curriedTensor :
    (curriedTensor (DerivedCategory (Mod C R))).IsLeftDerivedFunctor₂
      (Functor.LaxMonoidal.μNatTrans DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (Mod C R) (ComplexShape.up ℤ))
      (HomotopyCategory.quasiIso (Mod C R) (ComplexShape.up ℤ)) :=
  inferInstance

end CategoryTheory.Mod
