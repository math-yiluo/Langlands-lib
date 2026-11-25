/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Shift.Adjunction
import WeilConjectures.CategoryTheory.Adjunction.ProperBaseChange.AdjunctionSquareShiftMate

/-! # Shift compatibility of an isomorphism determined by a unit square -/

@[expose] public section
set_option autoImplicit false

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄
namespace CategoryTheory.Adjunction

/-- An invertible left comparison normalized by the unit square is the mate of
the right comparison, so it commutes with shifts whenever the latter does.
Source: Stacks 0A8D and 0037, adjoint shifts and the adjunct formulas
(blueprint: lem-pod-reduction-shift-from-limit-mate-s8).
Proof: cancel the right adjoint applied to the invertible left comparison in the
unit square. This identifies the adjunct of the inverse left comparison with the
unit followed by the right comparison. The inverse hom equivalence identifies
that inverse comparison with the mate. The generic shifted-mate identity proves
shift compatibility of the inverse; compatibility passes to the isomorphism. -/
theorem iso_commShift_of_unit_square
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} C'] [Category.{v₄} D']
    [HasShift C ℤ] [HasShift D ℤ] [HasShift C' ℤ] [HasShift D' ℤ]
    {L : C ⥤ D} {R : D ⥤ C} {L' : C' ⥤ D'} {R' : D' ⥤ C'}
    (adj : L ⊣ R) (adj' : L' ⊣ R') (r : C ⥤ C') (t : D ⥤ D')
    [L.CommShift ℤ] [R.CommShift ℤ] [L'.CommShift ℤ] [R'.CommShift ℤ]
    [r.CommShift ℤ] [t.CommShift ℤ]
    (hunit : ∀ n : ℤ,
      CommShift.CompatibilityUnit adj (L.commShiftIso n) (R.commShiftIso n))
    (hunit' : ∀ n : ℤ,
      CommShift.CompatibilityUnit adj' (L'.commShiftIso n) (R'.commShiftIso n))
    (e : L ⋙ t ≅ r ⋙ L') (β : R ⋙ r ⟶ t ⋙ R') [NatTrans.CommShift β ℤ]
    (h : ∀ P, r.map (adj.unit.app P) ≫ β.app (L.obj P) ≫
      R'.map (e.hom.app P) = adj'.unit.app (r.obj P)) :
    NatTrans.CommShift e.hom ℤ := by
  have hmate (P : C) : adj'.homEquiv (r.obj P) (t.obj (L.obj P)) (e.inv.app P) =
      r.map (adj.unit.app P) ≫ β.app (L.obj P) := by
    apply (cancel_mono (R'.map (e.hom.app P))).mp
    rw [adj'.homEquiv_unit, Category.assoc, ← R'.map_comp, Iso.inv_hom_id_app]
    change adj'.unit.app (r.obj P) ≫ R'.map (𝟙 (L'.obj (r.obj P))) = _
    erw [R'.map_id, Category.comp_id]
    simpa only [Category.assoc] using (h P).symm
  have htheta (P : C) :
      L'.map (r.map (adj.unit.app P) ≫ β.app (L.obj P)) ≫
        adj'.counit.app _ = e.inv.app P := by
    have hp := (adj'.homEquiv (r.obj P) (t.obj (L.obj P))).symm_apply_apply
      (e.inv.app P)
    rw [adj'.homEquiv_counit] at hp
    rw [hmate] at hp
    exact hp
  have : NatTrans.CommShift e.inv ℤ := by
    constructor
    intro n
    ext P
    have hm := (square_shift_mate adj adj' r t hunit hunit' β
      (fun A n ↦ by
        have hb := NatTrans.shift_app_comm β n A
        simpa only [Functor.commShiftIso_comp_hom_app, Category.assoc] using hb.symm)
      P n).2.2.2
    rw [htheta, htheta] at hm
    simpa only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.commShiftIso_comp_hom_app, Category.assoc] using hm.symm
  have hinv : NatTrans.CommShift e.symm.hom ℤ := inferInstanceAs
    (NatTrans.CommShift e.inv ℤ)
  exact NatTrans.CommShift.of_iso_inv e.symm ℤ

end CategoryTheory.Adjunction
