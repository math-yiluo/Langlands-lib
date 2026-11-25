/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Classical.ClassicalContinuityMapSupplement
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Classical module sheaves and complexes on the small pro-etale site

Source: the Weil conjectures blueprint, `definition-classical-pro-etale-sheaves`
(blueprint: definition-classical-pro-etale-sheaves).
-/

@[expose] public section

set_option autoImplicit false

universe u v

open CategoryTheory

namespace AlgebraicGeometry.ProEtale

/-- A module sheaf is classical when its underlying sheaf of sets is classical in the
continuity-map sense. Source: blueprint `definition-classical-pro-etale-sheaves`, final module
clause (blueprint: definition-classical-pro-etale-sheaves). -/
def IsClassicalModuleSheaf {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}}
    (F : SheafOfModules.{u + 1} R) : Prop :=
  IsClassical
    ((sheafCompose (Scheme.ProEt.topology X) (forget AddCommGrpCat.{u + 1})).obj
      ((SheafOfModules.toSheaf R).obj F))

/-- A complex of module sheaves is classical when every cohomology sheaf is classical.
Source: blueprint `definition-classical-pro-etale-sheaves`, final complex clause
(blueprint: definition-classical-pro-etale-sheaves). -/
def IsClassicalModuleComplex {X : Scheme.{u}}
    {R : Sheaf (Scheme.ProEt.topology X) RingCat.{u + 1}}
    [HasDerivedCategory (SheafOfModules.{u + 1} R)]
    (K : DerivedCategory (SheafOfModules.{u + 1} R)) : Prop :=
  ∀ q : ℤ,
    IsClassicalModuleSheaf
      ((DerivedCategory.homologyFunctor (SheafOfModules.{u + 1} R) q).obj K)

end AlgebraicGeometry.ProEtale
