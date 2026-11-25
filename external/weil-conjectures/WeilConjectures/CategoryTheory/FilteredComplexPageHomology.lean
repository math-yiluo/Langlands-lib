/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import Mathlib.CategoryTheory.Abelian.Exact
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorCyclesCover
import WeilConjectures.CategoryTheory.FilteredComplexSuccessorBoundariesImage

/-!
# Successor homology of a filtered-complex quotient page

Source: Stacks Project, Homology, Tag 012K, lemma-spectral-sequence-filtered-complex,
and the displayed cycle, boundary, and differential formulas preceding it.
(blueprint: lem-sp-filtered-complex-page-homology).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

private theorem pullback_kernel {A B T : C} (f : A ⟶ B) (g : B ⟶ T) :
    (Subobject.pullback f).obj (kernelSubobject g) = kernelSubobject (f ≫ g) := by
  apply le_antisymm
  · apply le_kernelSubobject
    have hf := (pullback_factors_iff f (kernelSubobject g) _).mp
      (Subobject.factors_self _)
    simpa only [Category.assoc] using (kernelSubobject_factors_iff g _).mp hf
  · apply Subobject.le_of_factors
    apply (pullback_factors_iff _ _ _).mpr
    apply kernelSubobject_factors
    simpa only [Category.assoc] using kernelSubobject_arrow_comp (f ≫ g)

/-- The homology of the representative differential is the next concrete quotient.
The next page's differential is not needed for this assertion.
Source: Stacks Project, Tag 012K, lemma-spectral-sequence-filtered-complex,
and the displayed cycle, boundary, and differential formulas preceding it.
(blueprint: lem-sp-filtered-complex-page-homology).

Proof. Work at (p,q), put n = p+q, and write R_s for
F^p K^n ∩ d⁻¹(F^(p+s) K^(n+1)) and T_s for
F^p K^n ∩ d(F^(p-s+1) K^(n-1)). The graded image of R_s is Z_s;
the graded image of T_s is B_s. In E_r = Z_r/B_r, the kernel of d_r
is Z_(r+1)/B_r. Indeed, if dx is an r-boundary in filtration degree
p+r modulo F^(p+r+1), locally lift its boundary expression as dy
with y in F^(p+1), and replace x by x-y. This does not change its
graded class and makes its differential lie in F^(p+r+1). Conversely
any such representative is killed by d_r. Here local lifting means
pulling back along an epimorphism, which suffices to compute image
subobjects in an arbitrary abelian category; no projectivity is used.
The image of the incoming d_r is B_(r+1)/B_r: its source has filtration
degree p-r, and its differential lies in F^p, exactly the condition
defining T_(r+1). The same image argument gives both containments.
The equation on representatives in D identifies these maps with its
differentials. Since d squared is zero, B_(r+1) lies in Z_(r+1).
Finally the abelian quotient-of-quotients isomorphism identifies
(Z_(r+1)/B_r)/(B_(r+1)/B_r) with Z_(r+1)/B_(r+1), the concrete
cokernel on the right. All image and quotient computations are
componentwise and use finite limits and cokernels only. -/
theorem filteredComplex_page_homology
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ) :
    Nonempty (D.page.homology pq ≅ filteredComplexPageObject K F (r + 1) pq) := by
  have hZ : F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) ≤
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
  exact ⟨hsc.gIsCokernel.coconePointUniqueUpToIso (colimit.isColimit _)⟩

end CategoryTheory
