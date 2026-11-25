/-
Copyright (c) 2025 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/
module

public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Homology.Additive

/-!
# Bicomplexes: functoriality in the category

Supplement to `Mathlib.Algebra.Homology.HomologicalBicomplex`, migrated from
the branch `jriou_localization` of Joël Riou's mathlib fork
(leanprover-community/mathlib4#25848), adapted to mathlib `v4.33.1`.

-/

@[expose] public section

open CategoryTheory Limits

variable {C D : Type*} [Category* C] [Category* D] [HasZeroMorphisms C] [HasZeroMorphisms D]
  (F : C ⥤ D)
  {I₁ I₂ : Type*} (c₁ : ComplexShape I₁) (c₂ : ComplexShape I₂)

namespace CategoryTheory

namespace Functor

/-- The functor `HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex₂ D c₁ c₂` induced
by a functor `F : C ⥤ D` which preserves zero morphisms. -/
abbrev mapHomologicalComplex₂ [F.PreservesZeroMorphisms] :
    HomologicalComplex₂ C c₁ c₂ ⥤ HomologicalComplex₂ D c₁ c₂ :=
  (F.mapHomologicalComplex c₂).mapHomologicalComplex c₁

end Functor

end CategoryTheory
