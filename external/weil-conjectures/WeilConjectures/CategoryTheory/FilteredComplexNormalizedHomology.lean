/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import Mathlib.CategoryTheory.Abelian.Exact
import all WeilConjectures.CategoryTheory.FilteredComplexPageHomology
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorCyclesCover
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorBoundariesImage

/-!
# The normalized successor homology comparison

Source: Stacks Project, Tag 012K, Lemma 12.24.2, the cycle and boundary formulas.
(blueprint: lem-sp-filtered-complex-normalized-homology).
-/

@[expose] public section

universe u v
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Normalize the homology comparison by its action on successor cycles.
Source: Stacks Project, Tag 012K, Lemma 12.24.2.
(blueprint: lem-sp-filtered-complex-normalized-homology). -/
def FilteredComplexHomologyNormalized
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ)
    (e : D.page.homology pq ≅ filteredComplexPageObject K F (r + 1) pq) : Prop :=
  ∀ (hZ : F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) ≤
        F.complexCycles pq.1 (pq.1 + pq.2) r)
    (f : (F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) : C) ⟶ D.page.cycles pq),
    f ≫ D.page.iCycles pq = Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ K F r pq →
    f ≫ D.page.homologyπ pq ≫ e.hom = filteredComplexPageπ K F (r + 1) pq

/-- Successor cycles are contained in the current cycles.
Source: Stacks Project, Tag 012K, the displayed formula for cycles.
(blueprint: lem-sp-filtered-complex-normalized-homology). -/
theorem filteredComplex_cycles_successor_le
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (pq : ℤ × ℤ) :
    F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) ≤
      F.complexCycles pq.1 (pq.1 + pq.2) r := by
  unfold DecreasingFiltration.complexCycles
  apply (Subobject.«exists» _).monotone
  apply (Subobject.pullback _).monotone
  apply sup_le_sup_right
  apply inf_le_inf_left
  apply (Subobject.pullback _).monotone
  unfold DecreasingFiltration.complexStep
  have hF := F.antitone_step (show pq.1 + r ≤ pq.1 + (r + 1) by omega)
  have hfac := congrArg (fun φ ↦ φ.f (pq.1 + pq.2 + 1))
    (Subobject.ofLE_arrow hF)
  rw [HomologicalComplex.comp_f] at hfac
  apply imageSubobject_le _
    (((Subobject.ofLE _ _ hF).f (pq.1 + pq.2 + 1)) ≫
      factorThruImageSubobject ((F.step (pq.1 + r)).arrow.f (pq.1 + pq.2 + 1)))
  rw [Category.assoc, imageSubobject_arrow_comp, hfac]

/-- There is exactly one successor homology isomorphism with this normalization.
Source: Stacks Project, Tag 012K, Lemma 12.24.2.
(blueprint: lem-sp-filtered-complex-normalized-homology).

Proof. The successor-cycle cover f is epic. The successor-boundary image formula
identifies the kernel of f followed by the homology projection with the image of
the successor boundary inclusion. Thus this composite is a cokernel of that
inclusion, as is the successor page projection. The unique comparison of these
two cokernels is the desired isomorphism. Its equation is independent of the
chosen cycle cover because the page cycle inclusion is monic. Cancelling the
epic composite f followed by the homology projection proves uniqueness. -/
theorem filteredComplex_normalized_homology
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ) :
    ∃! e : D.page.homology pq ≅ filteredComplexPageObject K F (r + 1) pq,
      FilteredComplexHomologyNormalized K F r D pq e := by
  have hZ := filteredComplex_cycles_successor_le K F r pq
  obtain ⟨f, hfepi, hf⟩ := filteredComplex_successor_cycles_cover K F r hr D pq hZ
  have : Epi f := hfepi
  let b := Subobject.ofLE _ _
    (filteredComplex_boundaries_le_cycles K F pq.1 (pq.1 + pq.2) (r + 1))
  let t := D.page.toCycles ((ComplexShape.up' (r, 1 - r)).prev pq) pq
  have ht : t ≫ D.page.homologyπ pq = 0 := D.page.toCycles_comp_homologyπ _ _
  have hker : kernelSubobject (D.page.homologyπ pq) = imageSubobject t := by
    exact ((ShortComplex.mk t (D.page.homologyπ pq) ht).exact_iff_image_eq_kernel.mp
      (ShortComplex.exact_of_g_is_cokernel _ (D.page.homologyIsCokernel _ _ rfl))).symm
  have himage := filteredComplex_successor_boundaries_image K F r hr D pq hZ f hf
  have heq : imageSubobject b = kernelSubobject (f ≫ D.page.homologyπ pq) := by
    rw [imageSubobject_mono, ← pullback_kernel, hker]
    exact himage.symm
  have w : b ≫ (f ≫ D.page.homologyπ pq) = 0 := by
    apply (kernelSubobject_factors_iff _ _).mp
    rw [← heq]
    simpa only [Category.id_comp] using imageSubobject_factors_comp_self b (𝟙 _)
  have hsc := (ShortComplex.mk b (f ≫ D.page.homologyπ pq) w).exact_iff_image_eq_kernel.mpr
    heq
  let e := hsc.gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _)
  have he : f ≫ D.page.homologyπ pq ≫ e.hom =
      filteredComplexPageπ K F (r + 1) pq := by
    rw [← Category.assoc]
    change (f ≫ D.page.homologyπ pq) ≫ e.hom = cokernel.π b
    exact
      hsc.gIsCokernel.comp_coconePointUniqueUpToIso_hom
        (colimit.isColimit _) WalkingParallelPair.one
  have hn : FilteredComplexHomologyNormalized K F r D pq e := by
    intro hZ' f' hf'
    have hff : f' = f := by
      apply (cancel_mono (D.page.iCycles pq)).1
      exact hf'.trans hf.symm
    simpa only [hff] using he
  refine ⟨e, hn, ?_⟩
  intro e' he'
  apply Iso.ext
  apply (cancel_epi (f ≫ D.page.homologyπ pq)).1
  simpa only [Category.assoc] using (he' hZ f hf).trans he.symm

end CategoryTheory
