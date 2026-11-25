/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.FilteredComplexPageDifferential
import WeilConjectures.CategoryTheory.FilteredComplexDifferentialRepresentativesCover

@[expose] public section
universe v u
open CategoryTheory CategoryTheory.Limits
namespace CategoryTheory
variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The successor-cycle inclusion into the page is killed by the outgoing page differential.
Source: Stacks Project, Homology, Tag 012K, displayed cycle and differential formulas.
(blueprint: lem-sp-filtered-complex-successor-cycles-differential-zero).

Proof. Put p = pq.1, n = pq.1 + pq.2, and j = (p+r, pq.2-r+1).
Take the intersection R = F^p K^n ∩ d⁻¹(F^(p+r+1) K^(n+1)), regarded as a
subobject of F^p K^n. Its graded projection factors epimorphically onto
Z_(r+1): adding F^(p+1) before projection does not change its image because
the projection kills F^(p+1). Write x for this epimorphism and t for the
inclusion of R into F^p K^n. The differential of t factors through
F^(p+r+1) K^(n+1); compose that factorization with the inclusion into
F^(p+r) K^(n+1), obtaining t'. The cokernel equation for the target graded
projection shows that t' has zero graded class. Apply D.on_representatives
to t, t', the composite of x with the inclusion hZ, and the zero target
cycle. The source representative equation follows from the image
factorization and Subobject.ofLE_arrow; the differential equation follows
from the factorization of dt; the target representative equation is the
cokernel equation just established. It follows that x followed by the
composite in the conclusion is zero. Cancel the epimorphism x to conclude.
All constructions are finite subobject and cokernel constructions and
require neither elementwise lifts through an epimorphism nor boundedness. -/
theorem filteredComplex_successor_cycles_differential_zero
    (K : CochainComplex C ℤ) (F : DecreasingFiltration K) (r : ℤ) (hr : 1 ≤ r)
    (D : FilteredComplexPageDifferential K F r) (pq : ℤ × ℤ)
    (hZ : F.complexCycles pq.1 (pq.1 + pq.2) (r + 1) ≤
      F.complexCycles pq.1 (pq.1 + pq.2) r) :
    (Subobject.ofLE _ _ hZ ≫ filteredComplexPageπ K F r pq) ≫
        D.page.d pq ((ComplexShape.up' (r, 1 - r)).next pq) = 0 := by
  have _hr := hr
  let j : ℤ × ℤ := pq + (r, 1 - r)
  have hij : (ComplexShape.up' (r, 1 - r)).Rel pq j := rfl
  rw [(ComplexShape.up' (r, 1 - r)).next_eq' hij]
  let k : ℤ × ℤ := (j.1 + 1, j.2 - 1)
  have hik : (ComplexShape.up' (r + 1, 1 - (r + 1))).Rel pq k := by
    change pq + (r + 1, 1 - (r + 1)) = k
    ext <;> dsimp [j, k] <;> omega
  obtain ⟨A, t, t', x, y, hx, hdt, hsrc, htgt⟩ :=
    filteredComplex_differential_representatives_cover K F (r + 1) pq k hik
  have hn : k.1 + k.2 = j.1 + j.2 := by dsimp [j, k]; omega
  have hex : ∃ s : A ⟶ (F.step k.1 : CochainComplex C ℤ).X (j.1 + j.2),
      t ≫ (F.step pq.1).arrow.f (pq.1 + pq.2) ≫
          K.d (pq.1 + pq.2) (j.1 + j.2) =
        s ≫ (F.step k.1).arrow.f (j.1 + j.2) := by
    rw [← hn]
    exact ⟨t', hdt⟩
  obtain ⟨t', hdt⟩ := hex
  let inc := Subobject.ofLE (F.step (j.1 + 1)) (F.step j.1)
    (F.antitone_step (by omega))
  have hinc : inc.f (j.1 + j.2) ≫ (F.step j.1).arrow.f (j.1 + j.2) =
      (F.step (j.1 + 1)).arrow.f (j.1 + j.2) := by
    exact congrArg (fun φ : (F.step (j.1 + 1) : CochainComplex C ℤ) ⟶ K ↦
      φ.f (j.1 + j.2)) (Subobject.ofLE_arrow _)
  have hdt' : t ≫ (F.step pq.1).arrow.f (pq.1 + pq.2) ≫
      K.d (pq.1 + pq.2) (j.1 + j.2) =
      (t' ≫ inc.f (j.1 + j.2)) ≫ (F.step j.1).arrow.f (j.1 + j.2) := by
    simpa only [Category.assoc, hinc] using hdt
  have hsrc' : (x ≫ Subobject.ofLE _ _ hZ) ≫
      (F.complexCycles pq.1 (pq.1 + pq.2) r).arrow =
      t ≫ (F.complexQuotientπ pq.1 (pq.1 + 1) (by omega)).f (pq.1 + pq.2) := by
    simpa only [Category.assoc, Subobject.ofLE_arrow] using hsrc
  have hzero : (t' ≫ inc.f (j.1 + j.2)) ≫
      (F.complexQuotientπ j.1 (j.1 + 1) (by omega)).f (j.1 + j.2) = 0 := by
    rw [Category.assoc]
    have hg : inc.f (j.1 + j.2) ≫
        (F.complexQuotientπ j.1 (j.1 + 1) (by omega)).f (j.1 + j.2) = 0 := by
      exact congrArg (fun φ : (F.step (j.1 + 1) : CochainComplex C ℤ) ⟶
        F.gradedPiece j.1 ↦ φ.f (j.1 + j.2)) (cokernel.condition inc)
    rw [hg, comp_zero]
  apply (cancel_epi x).1
  have hrep := D.on_representatives A pq j hij t (t' ≫ inc.f (j.1 + j.2))
    (x ≫ Subobject.ofLE _ _ hZ) 0 hdt' hsrc' (by simpa using hzero.symm)
  simpa only [Category.assoc, FilteredComplexPageDifferential.page,
    zero_comp, comp_zero] using hrep

end CategoryTheory
