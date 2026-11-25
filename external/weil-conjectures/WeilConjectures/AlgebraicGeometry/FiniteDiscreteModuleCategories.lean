/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.CategoryTheory.ModuleObjects.DerivedCategory
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.Def
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic

/-! # Categories for finite discrete coefficients, before bounded constructibility

These are the unchanged ordinary internal module and module-valued sheaf categories.
(auxiliary; not a blueprint node)
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.CondensedRing
variable (B : Type) [CommRing B] [TopologicalSpace B] [IsTopologicalRing B]

/-- Internal modules with the condensed continuous-function coefficient ring. -/
abbrev FiniteDiscreteInternalModules (T : Scheme.{u}) :=
  Mod (Sheaf (Scheme.ProEt.topology T) Ab.{u + 1})
    (condensedRingObj (Profinite.continuousMapRingObj.{u} B) T)

/-- Module-valued sheaves on the pro-etale site. -/
abbrev FiniteDiscreteProEtaleSheaves (T : Scheme.{u}) :=
  Sheaf (Scheme.ProEt.topology T) (ModuleCat.{u + 1} (ULift.{u + 1} B))

variable (T : Scheme.{u})
  (E : FiniteDiscreteProEtaleSheaves B T ≌ FiniteDiscreteInternalModules B T)

noncomputable instance finiteDiscreteEncoding_additive : E.functor.Additive :=
  Functor.additive_of_preserves_binary_products _

end AlgebraicGeometry.ProEtale.CondensedRing
