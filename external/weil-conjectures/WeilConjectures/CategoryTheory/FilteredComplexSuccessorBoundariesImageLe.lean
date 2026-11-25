/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
import WeilConjectures.CategoryTheory.FilteredComplexIncomingBoundaryQuotient
@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]
private theorem boundaries_mono (K : CochainComplex C ℤ)
    (F : DecreasingFiltration K) (p n r : ℤ) :
    F.complexBoundaries p n r ≤ F.complexBoundaries p n (r + 1) := by
  unfold DecreasingFiltration.complexBoundaries
  apply (Subobject.«exists» _).monotone
  apply (Subobject.pullback _).monotone
  apply sup_le_sup_right
  apply inf_le_inf_left
  apply (Subobject.«exists» _).monotone
  unfold DecreasingFiltration.complexStep
  have hF := F.antitone_step (show p - (r + 1) + 1 ≤ p - r + 1 by omega)
  have hfac := congrArg (fun φ ↦ φ.f (n - 1)) (Subobject.ofLE_arrow hF)
  rw [HomologicalComplex.comp_f] at hfac
  apply imageSubobject_le _
    (((Subobject.ofLE _ _ hF).f (n - 1)) ≫
      factorThruImageSubobject ((F.step (p - (r + 1) + 1)).arrow.f (n - 1)))
  rw [Category.assoc, imageSubobject_arrow_comp, hfac]

/-- Forward containment in the successor-boundaries image calculation.
Source: Stacks Project, Homology, Tag 012K.
(blueprint: new-filtered-complex-successor-boundaries-image-le).
The representative chase shows every pullback of an incoming page boundary is
represented by a successor boundary. -/
theorem filteredComplex_successor_boundaries_image_le
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ)
    (hZ : F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) ≤
      F.complexCycles pq.1 (pq.1 + pq.2) r)
    (f : (F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) : C) ⟶ D.page.cycles pq)
    (hf : f ≫ D.page.iCycles pq =
        Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ K F r pq) :
    (Subobject.pullback f).obj
      (imageSubobject (D.page.toCycles ((ComplexShape.up' (r, 1 - r)).prev pq) pq)) ≤
      Subobject.mk (Subobject.ofLE _ _
        (filteredComplex_boundaries_le_cycles K F pq.1 (pq.1 + pq.2) (r + 1))) := by
  let Z := F.complexCycles pq.1 (pq.1 + pq.2) r
  let Z' := F.complexCycles pq.1 (pq.1 + pq.2) (r + 1)
  let B := F.complexBoundaries pq.1 (pq.1 + pq.2) r
  let B' := F.complexBoundaries pq.1 (pq.1 + pq.2) (r + 1)
  have hBZ : B ≤ Z := filteredComplex_boundaries_le_cycles K F _ _ _
  have hB'Z' : B' ≤ Z' := filteredComplex_boundaries_le_cycles K F _ _ _
  have hB'Z : B' ≤ Z := hB'Z'.trans hZ
  have hBB' : B ≤ B' := boundaries_mono K F _ _ _
  let b := Subobject.ofLE B Z hBZ
  let b' := Subobject.ofLE B' Z hB'Z
  let c := Subobject.ofLE B' Z' hB'Z'
  let i := Subobject.ofLE Z' Z hZ
  have hb : Subobject.ofLE B B' hBB' ≫ b' = b := Subobject.ofLE_comp_ofLE _ _ _ _ _
  -- Quotient by the larger boundary subobject, via the existing page quotient.
  let q : filteredComplexPageObject K F r pq ⟶ cokernel b' :=
    cokernel.desc b (cokernel.π b') (by rw [← hb, Category.assoc, cokernel.condition,
      comp_zero])
  have hπ : filteredComplexPageπ K F r pq ≫ q = cokernel.π b' :=
    cokernel.π_desc _ _ _
  have hd : D.d ((ComplexShape.up' (r, 1 - r)).prev pq) pq ≫ q = 0 := by
    apply filteredComplex_incoming_boundary_quotient K F r hr D pq hB'Z _ q
    rw [hπ]
    exact cokernel.condition b'
  let P := (Subobject.pullback f).obj
    (imageSubobject (D.page.toCycles ((ComplexShape.up' (r, 1 - r)).prev pq) pq))
  have hPf := (pullback_factors_iff f _ P.arrow).mp (Subobject.factors_self P)
  have ht : D.page.toCycles ((ComplexShape.up' (r, 1 - r)).prev pq) pq ≫
      D.page.iCycles pq ≫ q = 0 := by
    rw [← Category.assoc, HomologicalComplex.toCycles_i]
    exact hd
  -- The pulled-back image is killed by this larger quotient.
  have hzero : P.arrow ≫ i ≫ cokernel.π b' = 0 := by
    rw [← hπ, ← Category.assoc i, ← hf, Category.assoc]
    have hkill := imageSubobject_arrow_comp_eq_zero ht
    have ha := Subobject.factorThru_arrow _ _ hPf
    rw [← Category.assoc P.arrow f, ← ha, Category.assoc, hkill, comp_zero]
  -- A monomorphism is the kernel of its cokernel; cancel the cycle inclusion.
  let a := Abelian.monoLift b' (P.arrow ≫ i) (by simpa only [Category.assoc] using hzero)
  apply Subobject.le_of_factors
  apply (Subobject.mk_factors_iff c P.arrow).mpr
  refine ⟨a, ?_⟩
  apply (cancel_mono i).1
  rw [Category.assoc]
  change a ≫ c ≫ i = P.arrow ≫ i
  have hc : c ≫ i = b' := Subobject.ofLE_comp_ofLE _ _ _ _ _
  rw [hc]
  exact Abelian.monoLift_comp _ _ _
end CategoryTheory
