/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Derived.Basic
public import WeilConjectures.AlgebraicGeometry.DerivedCategory

/-!
# Comparison of the two models of `D(𝒪_X)`

For a scheme `X`, the category `X.Modules` and the category
`SheafOfModules (moduleRings X.toRingedSpace)` are the same category, with two syntactically
different `Category` instances. The derived category `DerivedCategory X.Modules` uses the
instance `HasDerivedCategory.ofIsGrothendieckAbelian`, while `schemeDerivedCategory X` uses an
arbitrary `HasDerivedCategory.{w}` instance on `SheafOfModules (moduleRings X.toRingedSpace)`.
Both are localizations of the homotopy category at the quasi-isomorphisms, hence they are
equivalent, compatibly with the localization functors.

## Main definitions

* `AlgebraicGeometry.modulesQh X`: the localization functor of `DerivedCategory X.Modules`,
  as a functor on the homotopy category of `SheafOfModules (moduleRings X.toRingedSpace)`.
* `AlgebraicGeometry.schemeDerivedCategoryEquiv X`: the equivalence
  `schemeDerivedCategory X ≌ DerivedCategory X.Modules`.
* `AlgebraicGeometry.qhCompSchemeDerivedCategoryEquivFunctor X`: its compatibility with the
  localization functors.
-/

@[expose] public section

universe w u

open CategoryTheory

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The localization functor `K(𝒪_X) ⥤ DerivedCategory X.Modules`, seen on the homotopy category
of `SheafOfModules (moduleRings X.toRingedSpace)`, which is the homotopy category of
`X.Modules`. -/
noncomputable def modulesQh :
    HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ComplexShape.up ℤ) ⥤
      DerivedCategory X.Modules :=
  DerivedCategory.Qh (C := X.Modules)

instance : (modulesQh X).IsLocalization
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ)) :=
  inferInstanceAs ((DerivedCategory.Qh (C := X.Modules)).IsLocalization
    (HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)))

variable [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

/-- The equivalence `schemeDerivedCategory X ≌ DerivedCategory X.Modules` between the two
models of the derived category of `𝒪_X`-modules: both are localizations of the homotopy category
at the quasi-isomorphisms. -/
noncomputable def schemeDerivedCategoryEquiv :
    schemeDerivedCategory.{u, w} X ≌ DerivedCategory X.Modules :=
  Localization.uniq DerivedCategory.Qh (modulesQh X)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (ComplexShape.up ℤ))

/-- The equivalence `schemeDerivedCategoryEquiv X` is compatible with the localization
functors. -/
noncomputable def qhCompSchemeDerivedCategoryEquivFunctor :
    DerivedCategory.Qh ⋙ (schemeDerivedCategoryEquiv.{w} X).functor ≅ modulesQh X :=
  Localization.compUniqFunctor _ _ _

/-- The inverse of `schemeDerivedCategoryEquiv X` is compatible with the localization
functors. -/
noncomputable def modulesQhCompSchemeDerivedCategoryEquivInverse :
    modulesQh X ⋙ (schemeDerivedCategoryEquiv.{w} X).inverse ≅ DerivedCategory.Qh :=
  Localization.compUniqInverse _ _ _

/-- The equivalence `schemeDerivedCategoryEquiv X` is compatible with the functors from cochain
complexes. -/
noncomputable def qCompSchemeDerivedCategoryEquivFunctor :
    DerivedCategory.Q ⋙ (schemeDerivedCategoryEquiv.{w} X).functor ≅
      (DerivedCategory.Q (C := X.Modules) :
        CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ ⥤ _) :=
  Functor.isoWhiskerRight (DerivedCategory.quotientCompQhIso _).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (qhCompSchemeDerivedCategoryEquivFunctor X) ≪≫
    DerivedCategory.quotientCompQhIso X.Modules

end AlgebraicGeometry
