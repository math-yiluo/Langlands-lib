/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-! # Adjunction and naturality calculations for quotient reduction maps

Source: the quotient-unit characterization and compact-support naturality calculation
in Steps 2, 3 and 6 of `lem-coef-compact-support-quotient-cocycle`.
(blueprint: lem-coef-compact-support-quotient-transport).
-/

@[expose] public section
set_option autoImplicit false

namespace CategoryTheory.CompactSupportQuotient
open CategoryTheory

/-- The twice-transposed unit is the canonical left-adjoint composition isomorphism.
Source: blueprint quotient-unit and naturality calculation, Steps 2, 3 and 6
(blueprint: lem-coef-compact-support-quotient-transport). -/
theorem adjunct_isIso
    {C A B : Type*} [Category C] [Category A] [Category B]
    {Lm : C ⥤ A} {Rm : A ⥤ C} {Ln : C ⥤ B} {Rn : B ⥤ C}
    {L : A ⥤ B} {R : B ⥤ A}
    (am : Lm ⊣ Rm) (an : Ln ⊣ Rn) (a : L ⊣ R) (e : R ⋙ Rm ≅ Rn) (K : C) :
    IsIso ((a.homEquiv _ _).symm
      ((am.homEquiv _ _).symm (an.unit.app K ≫ e.inv.app (Ln.obj K)))) := by
  have he : (a.homEquiv _ _).symm
      ((am.homEquiv _ _).symm (an.unit.app K ≫ e.inv.app (Ln.obj K))) =
      (Adjunction.leftAdjointCompIso am a an e).hom.app K := by
    simp only [Adjunction.leftAdjointCompIso_hom_app, Adjunction.homEquiv_counit,
      Functor.map_comp, Category.assoc]
  rw [he]
  infer_instance

end CategoryTheory.CompactSupportQuotient
