/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-!
# Limits of sheaves of modules are computed sectionwise

This records, as a single statement, that the category of sheaves of modules over a sheaf of
rings has all small limits, and that these are preserved by the forgetful functor to presheaves
of modules and by the evaluations at the objects of the site, i.e. they are computed
sectionwise.
-/

@[expose] public section

universe v v' u u'

open CategoryTheory Limits

namespace SheafOfModules

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C} (R : Sheaf J RingCat.{u})

/-- **Limits of sheaves of modules are sectionwise.** The category of sheaves of `R`-modules
has all small limits; they are preserved by the forgetful functor to presheaves of `R`-modules
and by evaluation at every object `X` of the site, so the sections of a limit over `X` are the
limit of the `R(X)`-modules of sections over `X`.
(blueprint: `situation-conventions`) -/
theorem hasLimits_and_preservesLimits_evaluation :
    HasLimitsOfSize.{v, v} (SheafOfModules.{v} R) ∧
      PreservesLimitsOfSize.{v, v} (forget.{v} R) ∧
      ∀ X : Cᵒᵖ, PreservesLimitsOfSize.{v, v} (evaluation.{v} R X) :=
  ⟨inferInstance, inferInstance, fun _ ↦ inferInstance⟩

end SheafOfModules
