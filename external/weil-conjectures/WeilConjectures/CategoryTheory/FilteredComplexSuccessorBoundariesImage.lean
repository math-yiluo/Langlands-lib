/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.Filtration


public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorBoundariesImageLe
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorBoundariesImageGe
import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.CategoryTheory.FilteredComplexBoundariesLECycles
import WeilConjectures.CategoryTheory.CanonicalFiltration

/-!
# Successor boundaries are the inverse image of page boundaries

Source: Stacks Project, Homology, Tag 012K, displayed boundary and differential formulas.
(blueprint: lem-sp-filtered-complex-successor-boundaries-image).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The inverse image of the incoming page boundary subobject under the successor-cycle
projection is the successor boundary subobject inside successor cycles.
Source: Stacks Project, Homology, Tag 012K, the boundary and differential formulas preceding
lemma-spectral-sequence-filtered-complex.
(blueprint: lem-sp-filtered-complex-successor-boundaries-image).

Proof. Write n = p+q. The image of the incoming page differential consists of
classes of dx with x in F^(p-r)K^(n-1) and dx in F^pK^n. These are exactly the
classes defining B_(r+1), modulo B_r. Indeed, the incoming r-cycle condition at
filtration degree p-r is precisely that its differential lands in F^p. Use the
representative equation for D in both directions, locally lifting along the
epimorphic representative and quotient projections. The inverse image of this
incoming image under f is B_(r+1) inside Z_(r+1): the additional ambiguity B_r
already lies in B_(r+1). Both containments are
therefore equalities of subobjects. All lifts used here are pullbacks along
epimorphisms in the abelian category. -/
theorem filteredComplex_successor_boundaries_image
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ)
    (hZ : F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) ≤
      F.complexCycles pq.1 (pq.1 + pq.2) r)
    (f : (F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) : C) ⟶ D.page.cycles pq)
    (hf : f ≫ D.page.iCycles pq =
        Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ K F r pq) :
    (Subobject.pullback f).obj
      (imageSubobject (D.page.toCycles ((ComplexShape.up' (r, 1 - r)).prev pq) pq)) =
      Subobject.mk (Subobject.ofLE _ _
        (filteredComplex_boundaries_le_cycles K F pq.1 (pq.1 + pq.2) (r + 1))) :=
  by
    apply le_antisymm
    · exact filteredComplex_successor_boundaries_image_le K F r hr D pq hZ f hf
    · exact filteredComplex_successor_boundaries_image_ge K F r hr D pq hZ f hf

end CategoryTheory
