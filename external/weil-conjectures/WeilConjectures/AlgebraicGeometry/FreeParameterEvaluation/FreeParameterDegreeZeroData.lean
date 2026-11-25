/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FreeParameterEvaluation.FreeParameterEvaluationData
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusCompatibility
public import WeilConjectures.CategoryTheory.Monoidal.Instances.DerivedCategoryBraided
import WeilConjectures.CategoryTheory.RingObjects.Condensed.CondensedAction.CondensedActionInjectiveRestriction

/-! # Canonical free-parameter evaluation data and coherence.
Source: Stacks 08J7, 07A6, 07A7 (blueprint: def-sfb-free-parameter-degree-zero-data). -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale.FreeParameterEvaluation

section TensorComparison
variable {C : Type (u + 2)} [Category.{u + 1} C] [Abelian C]
  [IsGrothendieckAbelian.{u + 1} C] [HasDerivedCategory.{u + 1} C]
  [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalClosed C]
  [BraidedCategory C] [Abelian.HasFunctorialFlatResolution C]

attribute [local instance] DerivedCategory.braidedCategory'

end TensorComparison
variable (R : Profinite.CondensedRing.{u}) [IsCommMonObj R.X]

attribute [local instance] PointDerivedHom.pullMonoidal
attribute [local instance] DerivedCategory.braidedCategory'

end AlgebraicGeometry.ProEtale.FreeParameterEvaluation
