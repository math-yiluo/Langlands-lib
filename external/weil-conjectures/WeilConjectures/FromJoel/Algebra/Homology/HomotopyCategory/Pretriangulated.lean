/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# A triangulatedness criterion for functors from the homotopy category

Supplement to `Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Category Limits Pretriangulated

variable {C : Type*} [Category* C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace HomotopyCategory

lemma functor_from_isTriangulated_iff {D : Type*} [Category* D] [HasZeroObject D]
    [HasShift D ℤ] [Preadditive D] [∀ (n : ℤ), (shiftFunctor D n).Additive]
    [Pretriangulated D] (F : HomotopyCategory C (.up ℤ) ⥤ D) [F.CommShift ℤ] :
    F.IsTriangulated ↔ ∀ ⦃K L : CochainComplex C ℤ⦄ (f : K ⟶ L),
      F.mapTriangle.obj (CochainComplex.mappingCone.triangleh f) ∈ distTriang D := by
  constructor
  · intro _ _ _ f
    exact F.map_distinguished _ (mappingCone_triangleh_distinguished f)
  · intro hF
    constructor
    rintro T ⟨K, L, f, ⟨e⟩⟩
    exact isomorphic_distinguished _ (hF f) _ (F.mapTriangle.mapIso e)

end HomotopyCategory
