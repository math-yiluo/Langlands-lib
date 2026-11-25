/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.SpectralSequence.Basic
public import WeilConjectures.Algebra.Homology.FilteredComplexSubquotients
import WeilConjectures.CategoryTheory.FilteredComplexPageHomology

/-!
# Positive pages of a filtered complex

Source: Stacks Project, Homology, Tag 012K and Remark 12.18.2
(blueprint: lem-sp-filtered-complex-positive-pages).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The positive-page sequence, without its initial graded complex.
Source: Stacks Project, Homology, Tag 012K, proof of
`lemma-spectral-sequence-filtered-complex`, and `remark-differential-object-selfmap`.
(blueprint: lem-sp-filtered-complex-positive-pages).

Proof. For every positive integer r, form the actual cokernel of the boundary
inclusion into the cycles, using filteredComplex_boundaries_le_cycles. The latter
containment is proved directly from d squared = 0 using the image/pullback
adjunction. The uniquely specified representative differential supplied by
filteredComplex_page_differential_exists_unique makes these concrete objects
into an r-page complex. Its differential sends the class of z to the class of dz
in bidegree (p+r,q+1-r). The calculation filteredComplex_page_homology identifies
its homology at (p,q) with the corresponding concrete quotient at r+1. Assemble
these page complexes and homology isomorphisms into Mathlib's SpectralSequence
structure. The required page comparisons are identity isomorphisms, since the
page objects were constructed as precisely the stated cokernels. No infinite
coproducts, arbitrary page objects, or finite-filtration hypothesis are used.
-/
theorem filteredComplex_positive_spectralSequence
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) :
    ∃ E : CohomologicalSpectralSequence C 1,
      ∀ (p q r : ℤ) (hr : 1 ≤ r),
        ∃ hBZ : F.complexBoundaries p (p + q) r ≤ F.complexCycles p (p + q) r,
          Nonempty ((E.page r).X (p, q) ≅ cokernel (Subobject.ofLE _ _ hBZ)) := by
  classical
  have hD (r : ℤ) (hr : 1 ≤ r) : Nonempty (FilteredComplexPageDifferential K F r) := by
    obtain ⟨D, _, _⟩ := filteredComplex_page_differential_exists_unique K F r hr
    exact ⟨D⟩
  let D (r : ℤ) (hr : 1 ≤ r) := Classical.choice (hD r hr)
  let E : CohomologicalSpectralSequence C 1 :=
    { page := fun r hr => (D r hr).page
      iso := fun r r' pq hrr' hr =>
        (Classical.choice (filteredComplex_page_homology K F r hr (D r hr) pq)) ≪≫
          eqToIso (congrArg (fun s => filteredComplexPageObject K F s pq) hrr') }
  refine ⟨E, fun p q r hr => ?_⟩
  refine ⟨filteredComplex_boundaries_le_cycles K F p (p + q) r, ?_⟩
  exact ⟨Iso.refl _⟩

end CategoryTheory
