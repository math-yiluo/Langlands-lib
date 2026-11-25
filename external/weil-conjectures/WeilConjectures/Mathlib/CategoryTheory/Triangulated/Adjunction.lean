/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Triangulated.Adjunction
public import WeilConjectures.Mathlib.CategoryTheory.Triangulated.Generators

/-!
# The isomorphism locus of the unit of a triangulated adjunction

For an adjunction `F ⊣ G` of pretriangulated categories whose left adjoint `F` is triangulated,
the objects at which the unit `X ⟶ G (F X)` is an isomorphism form a triangulated subcategory:
`G` carries the shift structure making the adjunction compatible with the shifts
(`CategoryTheory.Adjunction.rightAdjointCommShift`), for which it is triangulated
(`CategoryTheory.Adjunction.isTriangulated_rightAdjoint`), and the unit is then a natural
transformation of triangulated functors compatible with the shifts.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Limits Pretriangulated

variable {C D : Type*} [Category* C] [Category* D] [HasZeroObject C] [HasZeroObject D]
  [Preadditive C] [Preadditive D] [HasShift C ℤ] [HasShift D ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [∀ n : ℤ, (shiftFunctor D n).Additive]
  [Pretriangulated C] [Pretriangulated D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  [F.CommShift ℤ] [F.IsTriangulated]

/-- For an adjunction `F ⊣ G` of pretriangulated categories with `F` triangulated, the objects at
which the unit of the adjunction is an isomorphism form a triangulated subcategory. -/
instance isTriangulated_isoLocus_unit : adj.unit.isoLocus.IsTriangulated := by
  let := adj.rightAdjointCommShift ℤ
  have := adj.commShift_of_leftAdjoint ℤ
  have := adj.isTriangulated_rightAdjoint
  infer_instance

end CategoryTheory.Adjunction
