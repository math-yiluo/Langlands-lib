/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import WeilConjectures.FromJoel.CategoryTheory.Abelian.Flat.Basic
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Dualizable objects are flat

In a braided monoidal category, tensoring with an object `X` which has a right dual has both a
left and a right adjoint, so it preserves all limits and colimits. In particular a dualizable
object is flat (`CategoryTheory.ObjectProperty.flat`).
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Limits

variable {C : Type*} [Category* C] [MonoidalCategory C] [BraidedCategory C]

/-- A dualizable object of a braided monoidal category is flat: tensoring with it preserves
finite limits and finite colimits. -/
theorem IsDualizable.flat {X : C} (hX : IsDualizable X) : ObjectProperty.flat X := by
  obtain ⟨_⟩ := hX
  let e : tensorLeft X ≅ tensorRight X := BraidedCategory.tensorLeftIsoTensorRight X
  have := (tensorLeftAdjunction X Xᘁ).rightAdjoint_preservesLimits
  have := (tensorRightAdjunction X Xᘁ).leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize (tensorLeft X) := preservesColimits_of_natIso e.symm
  have : PreservesLimitsOfSize (tensorRight X) := preservesLimits_of_natIso e
  exact ⟨(exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩,
    (exactFunctor_iff _).2 ⟨inferInstance, inferInstance⟩⟩

end CategoryTheory
