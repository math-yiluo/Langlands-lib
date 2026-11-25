/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.FromJoel.CategoryTheory.GradedObject.Colimits

/-!
# Supplement to limits in categories of homological complexes

Supplement to `Mathlib.Algebra.Homology.HomologicalComplexLimits`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

This provides the instances saying that the forgetful functor
`HomologicalComplex.forget C c` to graded objects preserves and reflects
colimits of shape `J` when `C` has colimits of shape `J`.

-/

@[expose] public section

open CategoryTheory Category Limits

namespace HomologicalComplex

variable {C ι J : Type*} [Category C] [Category J] {c : ComplexShape ι} [HasZeroMorphisms C]

instance [HasColimitsOfShape J C] :
    ReflectsColimitsOfShape J (HomologicalComplex.forget C c) where
  reflectsColimit := ⟨fun hc ↦ ⟨isColimitOfEval _ _ (fun i ↦
    isColimitOfPreserves (GradedObject.eval i) hc)⟩⟩

instance [HasColimitsOfShape J C] :
    PreservesColimitsOfShape J (HomologicalComplex.forget C c) where
  preservesColimit := ⟨fun hc ↦ ⟨GradedObject.evalJointlyReflectsColimits
    (fun i ↦ isColimitOfPreserves (eval _ _ i) hc)⟩⟩

end HomologicalComplex
