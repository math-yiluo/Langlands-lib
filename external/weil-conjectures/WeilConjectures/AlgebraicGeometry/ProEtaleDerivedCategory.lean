/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Derived category of modules on the small pro-etale site

Source: the Weil conjectures blueprint, `definition-small-pro-etale-site--1`, order 662
(blueprint: definition-small-pro-etale-site--1).
-/

@[expose] public section

universe t

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- (blueprint: definition-small-pro-etale-site--1) For a scheme `Y` and a commutative ring `A`,
the small pro-etale site is `Y.ProEt` with `ProEt.topology Y`: its objects are weakly
etale schemes over `Y`, and its covers are the pro-etale (fpqc) covering families.
The constant ring sheaf `A_Y` is the sheafification of the constant presheaf.
The category of sheaves of `A_Y`-modules is `SheafOfModules`; its derived category
is the localization of cochain complexes at quasi-isomorphisms (`HasDerivedCategory.standard`);
as an `abbrev` it carries the category and triangulated structure of `DerivedCategory`.

Source: the Weil conjectures blueprint, `definition-small-pro-etale-site--1`, order 662;
Stacks Project, Tag 098K (the small site) and Tag 05RU (the derived category). -/
noncomputable abbrev proEtaleDerivedCategory (Y : Scheme.{t})
    (A : Type t) [CommRing A] : Type _ :=
  @DerivedCategory
    (SheafOfModules.{t + 1}
      ((sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).obj
          ((constantSheaf (ProEt.topology Y) CommRingCat.{t + 1}).obj
            (CommRingCat.of (ULift.{t + 1, t} A)))))
    _ _ (HasDerivedCategory.standard _)

end AlgebraicGeometry.Scheme
