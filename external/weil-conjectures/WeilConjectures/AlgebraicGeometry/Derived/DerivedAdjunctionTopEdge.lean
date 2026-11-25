/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Derived.DerivedAdjunctionTopEdgeData
import WeilConjectures.AlgebraicGeometry.Derived.DerivedAdjunctionTopEdgeLocalCalculation

/-! # Top cohomology of the derived adjunction
The normalized local edge is identified with the counit on an upper truncation.
Adjunction naturality then gives its action on every bounded-above source.
Source: Stacks, derived.tex, Tags 08J5 and 05TC; cohomology.tex, Tags 079W and 0BKJ.
-/

@[expose] public section
set_option autoImplicit false
set_option linter.privateModule false
set_option synthInstance.maxSize 2048
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
noncomputable section
namespace AlgebraicGeometry

private theorem transpose_top_naturality
    {A B D E : Type*} [Category A] [Category B] [Category D] [Category E]
    (L : D ⥤ E) (R : E ⥤ D) (l : A ⥤ B) (r : B ⥤ A)
    (adj : L ⊣ R) (a : l ⊣ r) (H : D ⥤ A) (H' : E ⥤ B)
    {C P : D} {K : E} (f : C ⟶ P) (d : L.obj P ⟶ K)
    (kC : H'.obj (L.obj C) ⟶ l.obj (H.obj C))
    (kP : H'.obj (L.obj P) ⟶ l.obj (H.obj P)) [IsIso kC] [IsIso kP]
    (hk : H'.map (L.map f) ≫ kP = kC ≫ l.map (H.map f)) :
    a.homEquiv _ _ (inv kC ≫ H'.map ((adj.homEquiv _ _).symm
        (f ≫ adj.homEquiv _ _ d))) =
      H.map f ≫ a.homEquiv _ _ (inv kP ≫ H'.map d) := by
  have hi : inv kC ≫ H'.map (L.map f) = l.map (H.map f) ≫ inv kP := by
    apply (cancel_mono kP).1
    simpa only [Category.assoc, IsIso.inv_hom_id, Category.comp_id,
      IsIso.inv_hom_id_assoc] using congrArg (fun z ↦ inv kC ≫ z) hk
  rw [adj.homEquiv_naturality_left_symm, Equiv.symm_apply_apply, H'.map_comp]
  rw [← Category.assoc, hi, Category.assoc, a.homEquiv_naturality_left]

variable [∀ X : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]

end AlgebraicGeometry
