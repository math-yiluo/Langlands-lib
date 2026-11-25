/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingObjects.RingPresheaf
public import WeilConjectures.CategoryTheory.Sites.MonObj
import Mathlib.Algebra.Category.AlgCat.TensorAlgebra

/-! # The canonical ring object of a ring sheaf

Source: blueprint main-20261015, det-def-sfb-ring-object-sheaf.
(blueprint: det-def-sfb-ring-object-sheaf).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
universe u v w
open CategoryTheory CategoryTheory.MonoidalCategory
namespace CategoryTheory

/-- Forgetting a ring sheaf to abelian groups preserves the sheaf condition.
Source: det-def-sfb-ring-object-sheaf, first clause
(blueprint: det-def-sfb-ring-object-sheaf).
Proof: a matching family of underlying sections is exactly a matching family
of ring sections. Glue it uniquely in the ring sheaf. Addition, zero and negation
commute with this gluing by uniqueness, proving the abelian sheaf condition. -/
@[instance] theorem hasSheafCompose_forget₂_ringCat_ab
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C) :
    J.HasSheafCompose (forget₂ RingCat.{w} AddCommGrpCat.{w}) := by
  exact hasSheafCompose_of_preservesLimitsOfSize J

end CategoryTheory
