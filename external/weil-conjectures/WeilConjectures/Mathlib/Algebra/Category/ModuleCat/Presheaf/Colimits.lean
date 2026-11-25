/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits

/-!
# Colimits of presheaves of modules are computed sectionwise

This records, as a single statement, that the category of presheaves of modules over a
presheaf of rings has all small colimits, computed sectionwise, and that the forgetful functor
to presheaves of abelian groups preserves them.
-/

@[expose] public section

universe v v' u u'

open CategoryTheory Limits

namespace PresheafOfModules

variable {C : Type u'} [Category.{v'} C] (R : Cᵒᵖ ⥤ RingCat.{u})

/-- **Colimits of presheaves of modules are sectionwise.** The category of presheaves of
`R`-modules has all small colimits; evaluation at every object `X` preserves them (the sections
of a colimit over `X` are the colimit of the `R(X)`-modules of sections), and so does the
forgetful functor to presheaves of abelian groups.
(blueprint: `situation-conventions`) -/
theorem hasColimits_and_preservesColimits_evaluation :
    HasColimitsOfSize.{v, v} (PresheafOfModules.{v} R) ∧
      (∀ X : Cᵒᵖ, PreservesColimitsOfSize.{v, v} (evaluation.{v} R X)) ∧
      PreservesColimitsOfSize.{v, v} (toPresheaf.{v} R) :=
  ⟨inferInstance, fun _ ↦ inferInstance, inferInstance⟩

end PresheafOfModules
