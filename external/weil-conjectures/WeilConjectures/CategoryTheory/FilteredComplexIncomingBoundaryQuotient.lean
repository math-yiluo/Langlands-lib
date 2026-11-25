/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.CategoryTheory.FilteredComplexDifferentialRepresentativesCover
import WeilConjectures.Mathlib.CategoryTheory.Subobject.FactorThru

/-!
# Incoming differentials vanish modulo successor boundaries

Source: Stacks Project, Homology, Tag 012K, the displayed differential and boundary formulas.
(blueprint: new-filtered-complex-incoming-boundary-quotient).
-/

@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Any map out of a page that kills successor boundaries kills the incoming differential.
Source: Stacks Project, Homology, Tag 012K, the displayed differential and boundary formulas.
(blueprint: new-filtered-complex-incoming-boundary-quotient).

Proof. Write pq = (p,q), n = p+q. The preceding bidegree is
(p-r,q+r-1), of total degree n-1. Pull back along epimorphisms to lift
an arbitrary source page class first to graded r-cycles and then to an
unquotiented r-cycle x in F^(p-r) K^(n-1). Such lifts cover the source:
the page projection is a cokernel, and graded r-cycles are the image of
unquotiented r-cycles under the graded projection. In the latter assertion,
the extra F^(p-r+1) summand in the definition maps to zero.
The differential dx lies in F^p K^n by the r-cycle condition. It also lies
in d(F^(p-r) K^(n-1)), so its graded class belongs to B_(r+1) at (p,q).
It lies in Z_r since d squared is zero. Lift its graded class to B_(r+1)
after another epimorphic pullback, if necessary. The equation
D.on_representatives identifies the page differential of the class of x
with the page class of dx. The hypothesis hq kills this class, by the
inclusion of B_(r+1) into Z_r. The composite in the conclusion therefore
vanishes after an epimorphic cover of the source; cancel that epimorphism.
Only finite pullbacks and image factorizations are used, so this argument
does not assume projective objects or a concrete underlying category. -/
theorem filteredComplex_incoming_boundary_quotient
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ)
    (hB : F.complexBoundaries pq.1 (pq.1 + pq.2) (r + 1) ≤
      F.complexCycles pq.1 (pq.1 + pq.2) r)
    (Q : C) (q : filteredComplexPageObject K F r pq ⟶ Q)
    (hq : Subobject.ofLE _ _ hB ≫ filteredComplexPageπ K F r pq ≫ q = 0) :
    D.d ((ComplexShape.up' (r, 1 - r)).prev pq) pq ≫ q = 0 := by
  let i := (ComplexShape.up' (r, 1 - r)).prev pq
  have hi : (ComplexShape.up' (r, 1 - r)).Rel i pq := by
    have h : (ComplexShape.up' (r, 1 - r)).Rel (pq - (r, 1 - r)) pq :=
      sub_add_cancel _ _
    dsimp only [i]
    rw [(ComplexShape.up' (r, 1 - r)).prev_eq' h]
    exact h
  have hp : i.1 + r = pq.1 := congrArg (fun k : ℤ × ℤ ↦ k.1) hi
  have hn : pq.1 + pq.2 - 1 = i.1 + i.2 := by
    have hs := congrArg (fun k : ℤ × ℤ ↦ k.2) hi
    change i.2 + (1 - r) = pq.2 at hs
    omega
  have hfil : pq.1 - (r + 1) + 1 = i.1 := by
    have := hr
    omega
  obtain ⟨A, t, t', x, y, hepi, ht, hx, hy⟩ :=
    filteredComplex_differential_representatives_cover K F r i pq hi
  let m := (F.step pq.1).arrow.f (pq.1 + pq.2)
  let g := (F.complexQuotientπ pq.1 (pq.1 + 1) (by omega)).f (pq.1 + pq.2)
  let I := (Subobject.«exists» (K.d (pq.1 + pq.2 - 1) (pq.1 + pq.2))).obj
    (F.complexStep (pq.1 - (r + 1) + 1) (pq.1 + pq.2 - 1))
  let U := F.complexStep pq.1 (pq.1 + pq.2) ⊓ I
  let W := (Subobject.pullback m).obj
    (U ⊔ F.complexStep (pq.1 + 1) (pq.1 + pq.2))
  have hI : I.Factors (t' ≫ m) := by
    dsimp only [I]
    rw [hn, hfil]
    have h := (Subobject.exists_le_iff
      (K.d (i.1 + i.2) (pq.1 + pq.2))
      (F.complexStep i.1 (i.1 + i.2)) _).1 le_rfl
    have hf := imageSubobject_factors_comp_self ((F.step i.1).arrow.f (i.1 + i.2)) t
    rw [← ht]
    rw [← Category.assoc, ← Subobject.factorThru_arrow _ _ hf, Category.assoc]
    simpa only [Category.assoc, DecreasingFiltration.complexStep] using
      Subobject.factors_of_factors_right
        (Subobject.factorThru _ _ hf) h
  have hU : U.Factors (t' ≫ m) := by
    apply (Subobject.inf_factors _).2
    exact ⟨imageSubobject_factors_comp_self m t', hI⟩
  have hW : W.Factors t' := (pullback_factors_iff m _ _).2
    (Subobject.sup_factors_of_factors_left hU)
  let B := F.complexBoundaries pq.1 (pq.1 + pq.2) (r + 1)
  have hBfac : B.Factors (W.arrow ≫ g) :=
    (Subobject.exists_le_iff g W B).1 le_rfl
  have htB : B.Factors (t' ≫ g) := by
    rw [← Subobject.factorThru_arrow W t' hW, Category.assoc]
    exact Subobject.factors_of_factors_right _ hBfac
  let b := B.factorThru (t' ≫ g) htB
  have hyB : b ≫ Subobject.ofLE _ _ hB = y := by
    apply (cancel_mono (F.complexCycles pq.1 (pq.1 + pq.2) r).arrow).1
    simpa only [b, Category.assoc, Subobject.ofLE_arrow, Subobject.factorThru_arrow]
      using hy.symm
  have : Epi (filteredComplexPageπ K F r i) := by
    unfold filteredComplexPageπ
    infer_instance
  apply (cancel_epi (x ≫ filteredComplexPageπ K F r i)).1
  have hd := D.on_representatives A i pq hi t t' x y ht hx hy
  calc
    (x ≫ filteredComplexPageπ K F r i) ≫ (D.d i pq ≫ q) =
        y ≫ filteredComplexPageπ K F r pq ≫ q := by
      simpa only [Category.assoc] using congrArg (fun f ↦ f ≫ q) hd
    _ = 0 := by
      rw [← hyB, Category.assoc]
      exact (congrArg (fun f ↦ b ≫ f) hq).trans (comp_zero)
    _ = (x ≫ filteredComplexPageπ K F r i) ≫ 0 := by simp

end CategoryTheory
