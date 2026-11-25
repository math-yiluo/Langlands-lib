/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Mathlib.CategoryTheory.Endofunctor.Algebra
public import Mathlib.CategoryTheory.Limits.FullSubcategory

/-! # Created limits and colimits of fixed pairs

Source: the universal-property argument in step 5 of the twisted action-site proof,
with the existing algebra-limit construction.
(blueprint: lem-sf-twisted-fixed-pair-created-limits)
-/

@[expose] public section

set_option autoImplicit false

universe u v w w'

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Endofunctor.IsoAlgebra

variable {A : Type u} [Category.{v} A] (T : A ⥤ A)

/-- Limits of fixed pairs are created on their carriers when translation preserves limits.
Source: step 5 of the twisted action-site argument
(blueprint: lem-sf-twisted-fixed-pair-created-limits). -/
noncomputable instance forgetCreatesLimits [HasLimitsOfSize.{w, w'} A]
    [PreservesLimitsOfSize.{w, w'} T] : CreatesLimitsOfSize.{w, w'} (forget T) := by
  change CreatesLimitsOfSize.{w, w'} ((Algebra.IsIsoStr T).ι ⋙ Algebra.forget T)
  exact ⟨fun {J} _ ↦ inferInstance⟩

/-- Colimits of fixed pairs are created on their carriers when translation preserves colimits.
Source: step 5 of the twisted action-site argument
(blueprint: lem-sf-twisted-fixed-pair-created-limits). -/
noncomputable instance forgetCreatesColimits [HasColimitsOfSize.{w, w'} A]
    [PreservesColimitsOfSize.{w, w'} T] : CreatesColimitsOfSize.{w, w'} (forget T) := by
  change CreatesColimitsOfSize.{w, w'} ((Algebra.IsIsoStr T).ι ⋙ Algebra.forget T)
  exact ⟨fun {J} _ ↦ inferInstance⟩

end CategoryTheory.Endofunctor.IsoAlgebra
