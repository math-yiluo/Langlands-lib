/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorCyclesCoverExists
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorCyclesCoverEpi

/-!
# Successor cycles cover the kernel of a page differential

Source: Stacks Project, Homology, Tag 012K, displayed cycle and differential formulas.
(blueprint: lem-sp-filtered-complex-successor-cycles-cover).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The projection of successor graded cycles covers the cycles of the page differential.
Source: Stacks Project, Homology, Tag 012K, the cycle and differential formulas preceding
lemma-spectral-sequence-filtered-complex.
(blueprint: lem-sp-filtered-complex-successor-cycles-cover).

Proof. Write n = p+q. The composite from Z_(r+1) into Z_r/B_r is killed by d_r:
a representative has differential in F^(p+r+1), so its target graded class is zero.
The representative equation for D proves this after pulling back the epimorphism
from unquotiented representatives to graded cycles. Thus the composite factors
uniquely through the kernel, giving f. To see that f is epic, locally lift a page
cycle to an r-cycle representative x. Since its differential is an r-boundary in
the target graded piece, after another epimorphic pullback write dx = dy modulo
F^(p+r+1), with y in F^(p+1). Then x-y has the same source graded class and lies
in the (r+1)-cycle representatives. These local lifts show that the image of f is
the whole kernel. Pullbacks of epimorphisms remain epic in an abelian category,
so this proves the assertion without projectivity assumptions. -/
theorem filteredComplex_successor_cycles_cover
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ)
    (hZ : F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) ≤
      F.complexCycles pq.1 (pq.1 + pq.2) r) :
    ∃ f : (F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) : C) ⟶ D.page.cycles pq,
      Epi f ∧ f ≫ D.page.iCycles pq =
        Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ K F r pq := by
  obtain ⟨f, hf⟩ := filteredComplex_successor_cycles_cover_exists K F r hr D pq hZ
  exact ⟨f, filteredComplex_successor_cycles_cover_epi K F r hr D pq hZ f hf, hf⟩

end CategoryTheory
