/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# The limit functor as a limit of evaluation functors

The limit functor `lim : (K ⥤ C) ⥤ C` is the limit of the evaluation functors
`(evaluation K C).obj k`, with the projections `limit.π F k` as legs.
-/

@[expose] public section

universe v' v u' u

namespace CategoryTheory.Limits

variable (K : Type u') [Category.{v'} K] (C : Type u) [Category.{v} C] [HasLimitsOfShape K C]

/-- The cone over the evaluation functors `(evaluation K C).obj k` with point
`lim : (K ⥤ C) ⥤ C`, whose legs are the limit projections. -/
@[simps]
noncomputable def limConeEvaluation : Cone (evaluation K C) where
  pt := lim
  π := { app k := { app F := limit.π F k } }

/-- The cone `limConeEvaluation K C` is a limit cone. -/
noncomputable def isLimitLimConeEvaluation : IsLimit (limConeEvaluation K C) :=
  evaluationJointlyReflectsLimits _ fun F ↦ limit.isLimit F

end CategoryTheory.Limits
