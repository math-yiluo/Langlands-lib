/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Shifted maps under an adjunction whose left adjoint commutes with shifts

Let `adj : F ⊣ G` be an adjunction and suppose that `F` commutes with the shift by `A`. For
`X` in the source of `F`, `Y` in the target and `a : A`, maps `X ⟶ (G Y)⟦a⟧` correspond to
maps `F X ⟶ Y⟦a⟧`: a map `x` goes to `F x` followed by the commutation `F((G Y)⟦a⟧) ≅ (F G Y)⟦a⟧`
and the shift of the counit. No shift structure on `G` is needed.

## Main definitions

- `CategoryTheory.Adjunction.shiftedHomEquiv`: the bijection
  `(X ⟶ (G Y)⟦a⟧) ≃ (F X ⟶ Y⟦a⟧)`.
-/

@[expose] public section

namespace CategoryTheory.Adjunction

open Category

variable {C D : Type*} [Category* C] [Category* D] {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G)
  {A : Type*} [AddGroup A] [HasShift C A] [HasShift D A] [F.CommShift A]

/-- For an adjunction `F ⊣ G` with `F` commuting with the shifts, maps `X ⟶ (G Y)⟦a⟧`
correspond to maps `F X ⟶ Y⟦a⟧`: see `CategoryTheory.Adjunction.shiftedHomEquiv_apply` for the
formula. -/
noncomputable def shiftedHomEquiv (a : A) (X : C) (Y : D) :
    (X ⟶ (G.obj Y)⟦a⟧) ≃ (F.obj X ⟶ Y⟦a⟧) where
  toFun x := (adj.homEquiv _ _).symm (x ≫ (RightAdjointCommShift.iso adj a).inv.app Y)
  invFun y := adj.homEquiv _ _ y ≫ (RightAdjointCommShift.iso adj a).hom.app Y
  left_inv x := by simp
  right_inv y := by simp

lemma shiftedHomEquiv_apply (a : A) (X : C) (Y : D) (x : X ⟶ (G.obj Y)⟦a⟧) :
    adj.shiftedHomEquiv a X Y x =
      F.map x ≫ (F.commShiftIso a).hom.app (G.obj Y) ≫ (adj.counit.app Y)⟦a⟧' := by
  have h := CommShift.compatibilityCounit_of_compatibilityUnit adj _ _
    (RightAdjointCommShift.compatibilityUnit_iso adj a) Y
  change (adj.homEquiv _ _).symm (x ≫ (RightAdjointCommShift.iso adj a).inv.app Y) = _
  rw [homEquiv_counit, h, ← F.map_comp_assoc, assoc, Iso.inv_hom_id_app]
  exact congrArg (· ≫ _) (congrArg F.map (comp_id x))

end CategoryTheory.Adjunction
