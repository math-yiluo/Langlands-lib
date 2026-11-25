/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.FilteredComplexBoundariesLECycles
import WeilConjectures.CategoryTheory.FilteredComplexDifferentialRepresentativesCover
import WeilConjectures.CategoryTheory.FilteredComplexSingleDifferentialDescent

/-!
# Differentials on individual filtered-complex pages

Source: Stacks Project, Homology, Tag 012K, the displayed differential formula
preceding lemma-spectral-sequence-filtered-complex.
(blueprint: lem-sp-filtered-complex-page-differential).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual cycles/boundaries quotient in bidegree `pq`.
Source: Stacks Project, Tag 012K, the formula E = Z/B.
(blueprint: lem-sp-filtered-complex-page-differential). -/
noncomputable def filteredComplexPageObject (K : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (r : ℤ) (pq : ℤ × ℤ) : C :=
  cokernel (Subobject.ofLE _ _
    (filteredComplex_boundaries_le_cycles K F pq.1 (pq.1 + pq.2) r))

/-- Projection from the graded cycles to their quotient by boundaries.
Source: Stacks Project, Tag 012K, the formula E = Z/B.
(blueprint: lem-sp-filtered-complex-page-differential). -/
noncomputable def filteredComplexPageπ (K : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (r : ℤ) (pq : ℤ × ℤ) :
    (F.complexCycles pq.1 (pq.1 + pq.2) r : C) ⟶ filteredComplexPageObject K F r pq :=
  cokernel.π (Subobject.ofLE _ _
    (filteredComplex_boundaries_le_cycles K F pq.1 (pq.1 + pq.2) r))

/-- Differential data on one concrete quotient page. The representative equation
specifies the map by `z ↦ dz`; all page objects are already constructed cokernels.
Source: Stacks Project, Tag 012K, the displayed differential formula.
(blueprint: lem-sp-filtered-complex-page-differential). -/
structure FilteredComplexPageDifferential (K : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (r : ℤ) where
  d : ∀ i j : ℤ × ℤ,
    filteredComplexPageObject K F r i ⟶ filteredComplexPageObject K F r j
  shape : ∀ i j, ¬(ComplexShape.up' (r, 1 - r)).Rel i j → d i j = 0
  square_zero : ∀ i j k, d i j ≫ d j k = 0
  on_representatives : ∀ (A : C) (i j : ℤ × ℤ)
    (_ : (ComplexShape.up' (r, 1 - r)).Rel i j)
    (t : A ⟶ (F.step i.1 : CochainComplex C ℤ).X (i.1 + i.2))
    (t' : A ⟶ (F.step j.1 : CochainComplex C ℤ).X (j.1 + j.2))
    (x : A ⟶ (F.complexCycles i.1 (i.1 + i.2) r : C))
    (y : A ⟶ (F.complexCycles j.1 (j.1 + j.2) r : C)),
    t ≫ (F.step i.1).arrow.f (i.1 + i.2) ≫ K.d (i.1 + i.2) (j.1 + j.2) =
      t' ≫ (F.step j.1).arrow.f (j.1 + j.2) →
    x ≫ (F.complexCycles i.1 (i.1 + i.2) r).arrow =
      t ≫ (F.complexQuotientπ i.1 (i.1 + 1) (by omega)).f (i.1 + i.2) →
    y ≫ (F.complexCycles j.1 (j.1 + j.2) r).arrow =
      t' ≫ (F.complexQuotientπ j.1 (j.1 + 1) (by omega)).f (j.1 + j.2) →
    x ≫ filteredComplexPageπ K F r i ≫ d i j = y ≫ filteredComplexPageπ K F r j

private theorem filteredComplexPageDifferential_ext
    {K : CochainComplex C ℤ} {F : DecreasingFiltration K} {r : ℤ}
    {D E : FilteredComplexPageDifferential K F r} (h : D.d = E.d) : D = E := by
  cases D
  cases E
  congr

/-- Assemble the specified differential with the concrete quotient objects.
Source: Stacks Project, Tag 012K, the complexes (E_r,d_r).
(blueprint: lem-sp-filtered-complex-page-differential). -/
noncomputable def FilteredComplexPageDifferential.page
    {K : CochainComplex C ℤ} {F : DecreasingFiltration K} {r : ℤ}
    (D : FilteredComplexPageDifferential K F r) :
    HomologicalComplex C (ComplexShape.up' (r, 1 - r)) where
  X := filteredComplexPageObject K F r
  d := D.d
  shape := D.shape
  d_comp_d' i j k _ _ := D.square_zero i j k

set_option linter.unusedVariables false in
/-- The differential induced by K exists and is uniquely specified by its action
on filtered cycle representatives. This assertion concerns only one page; it
asserts neither a successor page nor a homology identification.
Source: Stacks Project, Tag 012K, the displayed differential formula preceding
lemma-spectral-sequence-filtered-complex.
(blueprint: lem-sp-filtered-complex-page-differential).

Proof. Put n = p+q. Restrict d to F^p K^n ∩ d⁻¹(F^(p+r) K^(n+1)).
It lands in F^(p+r) K^(n+1) ∩ ker d, hence in the target r-cycles. Project
there to the target quotient. Changing a representative by an element of
F^(p+1) that is an r-cycle changes its differential by an r-boundary in
filtration degree p+r: the allowed incoming filtration degree there is p+1.
Changing it by a source r-boundary has zero differential. The two cokernel
universal properties therefore descend d to the stated quotient map.
Put this map at related bidegrees and zero elsewhere. Its square is zero
because it is induced by d squared. For the displayed representative equation,
precompose the descended map with the cycle representative projection. This
projection is epic onto the graded cycles, and the cycles-to-page projection
is epic too; thus their composite is epic and the equation determines the
map uniquely. This is a componentwise finite-limit and cokernel construction,
valid without infinite sums or a finite-filtration assumption. -/
theorem filteredComplex_page_differential_exists_unique
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r) :
    ∃! D : FilteredComplexPageDifferential K F r, True := by
  classical
  have hex := fun i j hij ↦ filteredComplex_single_differential_descent K F r hr i j hij
  choose δ hδ using hex
  let d : ∀ i j : ℤ × ℤ,
      filteredComplexPageObject K F r i ⟶ filteredComplexPageObject K F r j :=
    fun i j ↦ if hij : (ComplexShape.up' (r, 1 - r)).Rel i j
    then δ i j hij else 0
  have hd (A : C) (i j : ℤ × ℤ) (hij : (ComplexShape.up' (r, 1 - r)).Rel i j)
      (t : A ⟶ (F.step i.1 : CochainComplex C ℤ).X (i.1 + i.2))
      (t' : A ⟶ (F.step j.1 : CochainComplex C ℤ).X (j.1 + j.2))
      (x : A ⟶ (F.complexCycles i.1 (i.1 + i.2) r : C))
      (y : A ⟶ (F.complexCycles j.1 (j.1 + j.2) r : C))
      (ht : t ≫ (F.step i.1).arrow.f (i.1 + i.2) ≫
        K.d (i.1 + i.2) (j.1 + j.2) = t' ≫ (F.step j.1).arrow.f (j.1 + j.2))
      (hx : x ≫ (F.complexCycles i.1 (i.1 + i.2) r).arrow =
        t ≫ (F.complexQuotientπ i.1 (i.1 + 1) (by omega)).f (i.1 + i.2))
      (hy : y ≫ (F.complexCycles j.1 (j.1 + j.2) r).arrow =
        t' ≫ (F.complexQuotientπ j.1 (j.1 + 1) (by omega)).f (j.1 + j.2)) :
      x ≫ filteredComplexPageπ K F r i ≫ d i j =
        y ≫ filteredComplexPageπ K F r j := by
    simpa only [d, dite_eq_left hij, filteredComplexPageπ, filteredComplexPageObject] using
      hδ i j hij A t t' x y ht hx hy
  have hshape (i j : ℤ × ℤ) (hij : ¬(ComplexShape.up' (r, 1 - r)).Rel i j) :
      d i j = 0 := by simp only [d, dite_eq_right hij]
  have hsquare (i j k : ℤ × ℤ) : d i j ≫ d j k = 0 := by
    by_cases hij : (ComplexShape.up' (r, 1 - r)).Rel i j
    · by_cases hjk : (ComplexShape.up' (r, 1 - r)).Rel j k
      · obtain ⟨A, t, t', x, y, hepi, ht, hx, hy⟩ :=
          filteredComplex_differential_representatives_cover K F r i j hij
        have : Epi (filteredComplexPageπ K F r i) := by
          unfold filteredComplexPageπ
          infer_instance
        apply (cancel_epi (x ≫ filteredComplexPageπ K F r i)).1
        have ht' : t' ≫ (F.step j.1).arrow.f (j.1 + j.2) ≫
            K.d (j.1 + j.2) (k.1 + k.2) =
            (0 : A ⟶ (F.step k.1 : CochainComplex C ℤ).X (k.1 + k.2)) ≫
              (F.step k.1).arrow.f (k.1 + k.2) := by
          calc
            _ = (t ≫ (F.step i.1).arrow.f (i.1 + i.2) ≫
                K.d (i.1 + i.2) (j.1 + j.2)) ≫
                K.d (j.1 + j.2) (k.1 + k.2) := by rw [ht, Category.assoc]
            _ = _ := by simp only [Category.assoc, K.d_comp_d, comp_zero, zero_comp]
        calc
          (x ≫ filteredComplexPageπ K F r i) ≫ (d i j ≫ d j k) =
              (y ≫ filteredComplexPageπ K F r j) ≫ d j k := by
            simpa only [Category.assoc] using
              congrArg (fun f ↦ f ≫ d j k) (hd A i j hij t t' x y ht hx hy)
          _ = 0 := by
            simpa only [Category.assoc, zero_comp] using
              hd A j k hjk t' 0 y 0 ht' hy (by simp)
          _ = (x ≫ filteredComplexPageπ K F r i) ≫ 0 := by simp
      · simp only [hshape j k hjk, comp_zero]
    · simp only [hshape i j hij, zero_comp]
  let D : FilteredComplexPageDifferential K F r :=
    ⟨d, hshape, hsquare, hd⟩
  refine ⟨D, trivial, ?_⟩
  intro E _
  have h : E.d = D.d := by
    funext i j
    by_cases hij : (ComplexShape.up' (r, 1 - r)).Rel i j
    · obtain ⟨A, t, t', x, y, hepi, ht, hx, hy⟩ :=
        filteredComplex_differential_representatives_cover K F r i j hij
      have : Epi (filteredComplexPageπ K F r i) := by
        unfold filteredComplexPageπ
        infer_instance
      apply (cancel_epi (x ≫ filteredComplexPageπ K F r i)).1
      simpa only [Category.assoc] using
        (E.on_representatives A i j hij t t' x y ht hx hy).trans
          (D.on_representatives A i j hij t t' x y ht hx hy).symm
    · exact (E.shape i j hij).trans (D.shape i j hij).symm
  exact filteredComplexPageDifferential_ext h

end CategoryTheory
