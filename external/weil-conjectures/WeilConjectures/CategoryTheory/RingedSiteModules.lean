/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian

/-!
# Module sheaves on an arbitrary ringed site

Source: Stacks Project, Modules on Sites, sheaves of modules and their abelian category
(auxiliary; not a blueprint node).

This public abbreviation makes the general-site specialization explicit. Its category,
linear morphisms and abelian instance are exactly Mathlib's, with no copied definition or
chosen categorical structure. The old recorded declaration applied only to schemes.
-/

@[expose] public section

universe v u vC uC

open CategoryTheory

namespace CategoryTheory

/-- Module sheaves on a general ringed site, using the existing Mathlib definition verbatim.

Source: Stacks Project, Modules on Sites, sheaves of modules
(auxiliary; not a blueprint node).
The objects are presheaves of modules with a sheaf condition; morphisms are the sectionwise
linear natural maps `SheafOfModules.Hom`. The inherited `SheafOfModules.instAbelian` applies
when sheafification and locally bijective equivalences are available, in particular on
small sites relative to the module universe. Kernels are sectionwise and cokernels are
sheafified sectionwise cokernels, as in Mathlib's sheafification-adjunction construction. -/
abbrev ringedSiteModules {C : Type uC} [Category.{vC} C]
    {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u}) :=
  SheafOfModules.{v} R

end CategoryTheory
