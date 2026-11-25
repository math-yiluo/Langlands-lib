/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorBoundaryRepresentatives
import WeilConjectures.Mathlib.CategoryTheory.Subobject.Limits
@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]
/-- Reverse containment in the successor-boundaries image calculation.
Source: Stacks Project, Homology, Tag 012K.
(blueprint: new-filtered-complex-successor-boundaries-image-ge).
The representative chase lifts each successor boundary to an incoming page
boundary, modulo the existing boundary ambiguity. -/
theorem filteredComplex_successor_boundaries_image_ge
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ)
    (hZ : F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) ≤
      F.complexCycles pq.1 (pq.1 + pq.2) r)
    (f : (F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) : C) ⟶ D.page.cycles pq)
    (hf : f ≫ D.page.iCycles pq =
        Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ K F r pq) :
      Subobject.mk (Subobject.ofLE _ _
        (filteredComplex_boundaries_le_cycles K F pq.1 (pq.1 + pq.2) (r + 1))) ≤
      (Subobject.pullback f).obj
      (imageSubobject (D.page.toCycles ((ComplexShape.up' (r, 1 - r)).prev pq) pq)) := by
  let i := (ComplexShape.up' (r, 1 - r)).prev pq
  have hi : (ComplexShape.up' (r, 1 - r)).Rel i pq := by
    change (ComplexShape.up' (r, 1 - r)).Rel
      ((ComplexShape.up' (r, 1 - r)).prev pq) pq
    have h : (ComplexShape.up' (r, 1 - r)).Rel (pq - (r, 1 - r)) pq := by
      exact sub_add_cancel _ _
    rw [(ComplexShape.up' (r, 1 - r)).prev_eq' h]
    exact h
  obtain ⟨A, e, he, t, t', x, hdt, hx, hy⟩ :=
    filteredComplex_successor_boundary_representatives K F r hr i pq hi
  let := he
  let b := Subobject.ofLE _ _
    (filteredComplex_boundaries_le_cycles K F pq.1 (pq.1 + pq.2) (r + 1))
  have hy' : (e ≫ b ≫ Subobject.ofLE _ _ hZ) ≫
      (F.complexCycles pq.1 (pq.1 + pq.2) r).arrow =
      t' ≫ (F.complexQuotientπ pq.1 (pq.1 + 1) (by omega)).f (pq.1 + pq.2) := by
    simpa only [b, Category.assoc, Subobject.ofLE_arrow] using hy
  have hd := D.on_representatives A i pq hi t t'
    x (e ≫ b ≫ Subobject.ofLE _ _ hZ) hdt hx hy'
  have hfactor : e ≫ b ≫ f =
      (x ≫ filteredComplexPageπ K F r i) ≫ D.page.toCycles i pq := by
    apply (cancel_mono (D.page.iCycles pq)).1
    simp only [Category.assoc, hf, HomologicalComplex.toCycles_i]
    simpa only [Category.assoc, FilteredComplexPageDifferential.page] using hd.symm
  apply (Subobject.mk_le_iff_factors _ _).2
  apply (pullback_factors_iff f _ _).2
  apply (Subobject.imageSubobject_le_iff _ _).1
  rw [← imageSubobject_comp_of_epi e (b ≫ f)]
  rw [hfactor]
  exact imageSubobject_comp_le _ _
end CategoryTheory
