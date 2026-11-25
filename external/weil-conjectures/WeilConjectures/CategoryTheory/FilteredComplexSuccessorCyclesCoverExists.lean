/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorCyclesDifferentialZero

@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The successor-cycle inclusion into the page factors through its cycles.
Source: Stacks Project, Homology, Tag 012K, displayed cycle, boundary and
differential formulas preceding lemma-spectral-sequence-filtered-complex.
(blueprint: lem-sp-filtered-complex-successor-cycles-cover-exists).

Proof. Put p = pq.1, n = pq.1 + pq.2 and j = (p+r,pq.2-r+1). Let a be the
successor-cycle inclusion followed by the page quotient projection. The image
factorization defining graded successor cycles gives an epimorphism from their
unquotiented representatives onto them: adding F^(p+1) does not change this image
because the graded projection kills F^(p+1). On these representatives, dx lies in
F^(p+r+1). Regard dx as a representative in F^(p+r); its graded class is zero, so
in D.on_representatives take the target graded cycle to be zero. This gives
(a followed by D.d pq j) = 0 after the representative epimorphism, hence before
it by cancellation. The kernel universal property, HomologicalComplex.liftCycles,
now gives f with f followed by D.page.iCycles pq equal to a. No epimorphy claim
about f is needed for this factorization. -/
theorem filteredComplex_successor_cycles_cover_exists
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ)
    (hZ : F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) ≤
      F.complexCycles pq.1 (pq.1 + pq.2) r) :
    ∃ f : (F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) : C) ⟶ D.page.cycles pq,
      f ≫ D.page.iCycles pq =
        Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ K F r pq := by
  let a := Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ K F r pq
  have ha : a ≫ D.page.d pq ((ComplexShape.up' (r, 1 - r)).next pq) = 0 := by
    exact filteredComplex_successor_cycles_differential_zero K F r hr D pq hZ
  let f := D.page.liftCycles a ((ComplexShape.up' (r, 1 - r)).next pq) rfl ha
  refine ⟨f, ?_⟩
  exact D.page.liftCycles_i a _ rfl ha

end CategoryTheory
