/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerInjectiveComponents
public import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantRingOperations
public import Mathlib.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlus
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.PlusExact
import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Coseparator
import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
import Mathlib.CategoryTheory.Limits.FullSubcategory
import Mathlib.CategoryTheory.Functor.ReflectsIso.Limits
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityLevelPullbackExact
import WeilConjectures.AlgebraicGeometry.Smooth.SmoothPurityTowerPushRightExtension

set_option linter.privateModule false

/-!
# Levels of the smooth-purity tower direct image

Source: blueprint main-20261015, chap-Smooth-purity, prose-09-23,
statement and its three proof paragraphs (blueprint: prose-09-23).

All indices n denote the positive level n+1. The module category is the recorded
varying-coefficient tower category, with its original small pro-etale site and
coefficient universe max u (t+1). Direct image is precomposition with base change,
with the scalar action induced by the constant-section map. No completion is taken.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall

universe t u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.ProEtale

variable (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
  [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]

variable {T S : Scheme.{t}} (g : T ⟶ S)

end AlgebraicGeometry.ProEtale

attribute [instance high] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
