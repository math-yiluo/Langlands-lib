/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.CategoryTheory.Shift.Adjunction

/-!
# Shift compatibility of the mate of an adjunction square

Source: Stacks Project, Tag 0A8D, `lemma-adjoint-is-exact`, adjoint shift construction;
Tag 0037, `definition-adjoint`, adjunct formulas. The four-category refinement and its
explicit adjunct equations are agent-written (blueprint: lem-weil-pbc-adjunction-square-shift-mate).
-/

@[expose] public section

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

namespace CategoryTheory.Adjunction

/-- Shift compatibility passes from a right comparison to its left mate, with both
shifted adjunct formulas. Here `h_P` is expanded as `r.map (adj.unit.app P) ≫ β.app (L.obj P)`,
its adjunct `θ_P` as `L'.map h_P ≫ adj'.counit.app (t.obj (L.obj P))`, and `d_P` as the
composite comparison for `L ⋙ t`.

Source: Stacks Project, Tags 0A8D and 0037; the four-category refinement is agent-written
(blueprint: lem-weil-pbc-adjunction-square-shift-mate).

Proof plan:
1. Expand `h` and `d`. Naturality of `β` at the shift comparison of `L`, the shift
   equation for `β`, the unprimed unit equation, and naturality of the comparison of `r`
   give the first equality. This uses the composite comparison convention of
   `lem-weil-pbc-commshift-nattrans-comp-whisker`.
2. By `lem-weil-pbc-adjunction-of-natural-bijection`, `adj'.homEquiv` sends `θ_P` to `h_P`;
   its inverse sends `h_P` to `L'.map h_P ≫ adj'.counit.app _` and it is injective.
3. Target naturality of this hom equivalence gives the first shifted adjunct formula.
4. By `lem-weil-pbc-adjunction-shift-compatibility-unique`, the primed unit equation
   implies the primed counit equation. Apply the inverse hom equivalence to the inverse
   right shift comparison followed by the shifted `h_P` and the comparison of `r`.
   Substitute the counit equation, cancel the right shift comparison with its inverse,
   and use naturality of the left shift comparison at `h_P`. This gives the second
   shifted map; apply the hom equivalence to obtain its requested adjunct formula.
5. Cancel the right shift comparison in the first equality. The two adjunct formulas
   now have equal right sides, so injectivity of `adj'.homEquiv` gives the mate equation.
Only shift comparisons are inverted; no invertibility of `β` or its mate is used. -/
theorem square_shift_mate
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
    (β : R ⋙ r ⟶ t ⋙ R')
    (hβ : ∀ (E : D) (n : ℤ),
      β.app (E⟦n⟧) ≫ R'.map ((t.commShiftIso n).hom.app E) ≫
          (R'.commShiftIso n).hom.app (t.obj E) =
        r.map ((R.commShiftIso n).hom.app E) ≫
          (r.commShiftIso n).hom.app (R.obj E) ≫ (β.app E)⟦n⟧')
    (P : C) (n : ℤ) :
    ((r.map (adj.unit.app (P⟦n⟧)) ≫ β.app (L.obj (P⟦n⟧))) ≫
        R'.map (t.map ((L.commShiftIso n).hom.app P) ≫
          (t.commShiftIso n).hom.app (L.obj P)) ≫
        (R'.commShiftIso n).hom.app (t.obj (L.obj P)) =
      (r.commShiftIso n).hom.app P ≫
        (r.map (adj.unit.app P) ≫ β.app (L.obj P))⟦n⟧') ∧
    (adj'.homEquiv (r.obj (P⟦n⟧)) ((t.obj (L.obj P))⟦n⟧)
        ((L'.map (r.map (adj.unit.app (P⟦n⟧)) ≫ β.app (L.obj (P⟦n⟧))) ≫
          adj'.counit.app (t.obj (L.obj (P⟦n⟧)))) ≫
          (t.map ((L.commShiftIso n).hom.app P) ≫
            (t.commShiftIso n).hom.app (L.obj P))) =
      (r.map (adj.unit.app (P⟦n⟧)) ≫ β.app (L.obj (P⟦n⟧))) ≫
        R'.map (t.map ((L.commShiftIso n).hom.app P) ≫
          (t.commShiftIso n).hom.app (L.obj P))) ∧
    (adj'.homEquiv (r.obj (P⟦n⟧)) ((t.obj (L.obj P))⟦n⟧)
        (L'.map ((r.commShiftIso n).hom.app P) ≫
          (L'.commShiftIso n).hom.app (r.obj P) ≫
          (L'.map (r.map (adj.unit.app P) ≫ β.app (L.obj P)) ≫
            adj'.counit.app (t.obj (L.obj P)))⟦n⟧') =
      (r.commShiftIso n).hom.app P ≫
        (r.map (adj.unit.app P) ≫ β.app (L.obj P))⟦n⟧' ≫
        (R'.commShiftIso n).inv.app (t.obj (L.obj P))) ∧
    ((L'.map (r.map (adj.unit.app (P⟦n⟧)) ≫ β.app (L.obj (P⟦n⟧))) ≫
        adj'.counit.app (t.obj (L.obj (P⟦n⟧)))) ≫
        (t.map ((L.commShiftIso n).hom.app P) ≫
          (t.commShiftIso n).hom.app (L.obj P)) =
      L'.map ((r.commShiftIso n).hom.app P) ≫
        (L'.commShiftIso n).hom.app (r.obj P) ≫
        (L'.map (r.map (adj.unit.app P) ≫ β.app (L.obj P)) ≫
          adj'.counit.app (t.obj (L.obj P)))⟦n⟧') := by
  let h (X : C) : r.obj X ⟶ R'.obj (t.obj (L.obj X)) := r.map (adj.unit.app X) ≫ β.app (L.obj X)
  let θ (X : C) : L'.obj (r.obj X) ⟶ t.obj (L.obj X) :=
    L'.map (h X) ≫ adj'.counit.app (t.obj (L.obj X))
  let d : t.obj (L.obj (P⟦n⟧)) ⟶ (t.obj (L.obj P))⟦n⟧ := t.map ((L.commShiftIso n).hom.app P) ≫
    (t.commShiftIso n).hom.app (L.obj P)
  have hθ (X : C) : adj'.homEquiv _ _ (θ X) = h X := by
    dsimp only [θ]
    simpa only [adj'.homEquiv_counit] using
      (adj'.homEquiv (r.obj X) (t.obj (L.obj X))).apply_symm_apply (h X)
  have hh : h (P⟦n⟧) ≫ R'.map d ≫
      (R'.commShiftIso n).hom.app (t.obj (L.obj P)) =
      (r.commShiftIso n).hom.app P ≫ (h P)⟦n⟧' := by
    dsimp only [h, d]
    simp only [Functor.map_comp, Category.assoc]
    have hb := β.naturality ((L.commShiftIso n).hom.app P)
    dsimp only [Functor.comp_map] at hb
    rw [← reassoc_of% hb]
    rw [hβ (L.obj P) n]
    simp only [← r.map_comp_assoc]
    rw [← Category.assoc, ← hunit n P]
    have hr := r.commShiftIso_hom_naturality (adj.unit.app P) n
    dsimp only [Functor.comp_obj, Functor.id_obj] at hr
    rw [hr]
    simp only [Category.assoc]
  have hfirst : adj'.homEquiv _ _ (θ (P⟦n⟧) ≫ d) =
      h (P⟦n⟧) ≫ R'.map d := by
    rw [adj'.homEquiv_naturality_right, hθ]
  have hsecond : adj'.homEquiv _ _
      (L'.map ((r.commShiftIso n).hom.app P) ≫
        (L'.commShiftIso n).hom.app (r.obj P) ≫ (θ P)⟦n⟧') =
      (r.commShiftIso n).hom.app P ≫ (h P)⟦n⟧' ≫
        (R'.commShiftIso n).inv.app (t.obj (L.obj P)) := by
    apply (adj'.homEquiv _ _).eq_symm_apply.mp
    rw [adj'.homEquiv_counit]
    rw [CommShift.compatibilityCounit_of_compatibilityUnit adj'
      (L'.commShiftIso n) (R'.commShiftIso n) (hunit' n)]
    simp only [Functor.map_comp, Category.assoc]
    simp only [← L'.map_comp_assoc, Iso.inv_hom_id_app]
    dsimp only [Functor.comp_obj, Functor.id_obj]
    simp only [Category.comp_id]
    simp only [Functor.map_comp, Category.assoc]
    rw [L'.commShiftIso_hom_naturality_assoc (h P) n]
    simp only [θ, Functor.map_comp]
  refine ⟨hh, hfirst, hsecond, ?_⟩
  change θ (P⟦n⟧) ≫ d = L'.map ((r.commShiftIso n).hom.app P) ≫
    (L'.commShiftIso n).hom.app (r.obj P) ≫ (θ P)⟦n⟧'
  apply (adj'.homEquiv _ _).injective
  refine hfirst.trans (Eq.trans ?_ hsecond.symm)
  apply (cancel_mono ((R'.commShiftIso n).hom.app (t.obj (L.obj P)))).mp
  simp only [Category.assoc, Iso.inv_hom_id_app]
  dsimp only [Functor.comp_obj]
  simpa only [Category.comp_id] using hh

end CategoryTheory.Adjunction
