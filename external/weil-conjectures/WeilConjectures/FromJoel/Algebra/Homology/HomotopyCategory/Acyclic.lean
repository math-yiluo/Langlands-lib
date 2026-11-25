/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic
public import WeilConjectures.FromJoel.CategoryTheory.Triangulated.HomologicalFunctor

/-!
# The subcategory of acyclic complexes is stable under retracts

Supplement to `Mathlib.Algebra.Homology.HomotopyCategory.Acyclic`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Limits

universe v u

variable (C : Type u) [Category.{v} C] [Abelian C]

namespace HomotopyCategory

instance : (subcategoryAcyclic C).IsStableUnderRetracts := by
  dsimp only [subcategoryAcyclic]
  infer_instance

instance quasiIso_respectsIso : (quasiIso C (ComplexShape.up ℤ)).RespectsIso := by
  rw [quasiIso_eq_trW_subcategoryAcyclic]
  infer_instance

end HomotopyCategory
