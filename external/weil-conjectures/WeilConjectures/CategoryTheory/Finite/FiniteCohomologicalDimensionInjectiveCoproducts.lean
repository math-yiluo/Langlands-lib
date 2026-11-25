/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Acyclic
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
import WeilConjectures.CategoryTheory.DerivedCategory.FiniteCohomologicalDimension

/-! # The injective-coproduct form of finite-dimensional derived continuity -/

@[expose] public section

universe w

open CategoryTheory Limits

namespace CategoryTheory.Functor

set_option autoImplicit false

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F]

end CategoryTheory.Functor
