/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StageSystem.Basic
public import Mathlib.CategoryTheory.Triangulated.Functor

/-! # Common-stage cone triangles

Source: blueprint `sec-proper-base-change/sk-thm-properbasechange`, common-stage cones
(blueprint: def-weil-pbc-common-stage-cones).
The construction is stated for the directed exact stage system supplied by that node.
Its application has finite coefficient fields as indices and the raw rational stages.
-/

@[expose] public section
set_option autoImplicit false

universe w v u
open CategoryTheory CategoryTheory.Pretriangulated
namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I]
  {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)
  [∀ i, HasShift (C i) ℤ] [HasShift S.PairCategory ℤ]
  [∀ i, (S.ι i).CommShift ℤ]

variable [∀ i, Preadditive (C i)] [∀ i, Limits.HasZeroObject (C i)]
  [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive] [∀ i, Pretriangulated (C i)]

/-- The distinguished triangles are precisely the isomorphic images of distinguished
finite-stage triangles. This is equivalently the common-stage cone criterion, since
isoToStage identifies the first two pairs with their common-stage representatives.
Source: blueprint common-stage cones (blueprint: def-weil-pbc-common-stage-cones). -/
def CommonStageDistinguished (T : Triangle S.PairCategory) : Prop :=
  ∃ (i : I) (U : Triangle (C i)),
    U ∈ distTriang (C i) ∧ Nonempty (T ≅ (S.ι i).mapTriangle.obj U)

end CategoryTheory.StageSystem
