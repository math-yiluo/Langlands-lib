/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Noetherian
public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure
import WeilConjectures.AlgebraicGeometry.StrictPerfectTensorLocalCohomology
import WeilConjectures.AlgebraicGeometry.CoherentModuleLocalOnOpenCover
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Data.Finset.Max

/-! # Bounded coherent cohomology of a perfect tensor

Source: Stacks Project, Tags 0DJQ and 01Y0
(blueprint: lem-pc-perfect-tensor-bounded-coherent).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits MonoidalCategory

namespace AlgebraicGeometry.Scheme

/-- Tensoring with a perfect object preserves bounded coherent cohomology on a
Noetherian scheme, without any relative flatness or proper-support hypothesis.
Source: Stacks Project, Tag 0DJQ, proof of Lemma 36.27.2 (local tensor calculation),
and Tag 01Y0 (closure of coherent sheaves under kernels and cokernels).

Proof:
1. Take a finite open cover of X with strictly perfect representatives P for E. Such a
   finite cover exists by compactness of X and the definition of IsPerfect. Write [c,d]
   for the bounds of G and [a_j,b_j] for those of each representative on the finite cover.
2. The terms of P are summands of finite free modules, hence flat. Thus the restriction
   of the derived tensor is represented by the ordinary total tensor complex P tensor G.
   Its degree n terms are summands of finite sums of coherent terms of G, hence coherent.
   Kernel and cokernel closure (01Y0) makes its cohomology coherent. Coherence is local,
   so the global cohomology sheaves are coherent.
3. The j-th total tensor vanishes outside [a_j+c,b_j+d]. Choose one interval containing
   these finitely many intervals. Vanishing of cohomology is local, giving global bounds.
   If X is empty, every sheaf is zero and any interval suffices.
(blueprint: lem-pc-perfect-tensor-bounded-coherent). -/
theorem perfect_tensor_bounded_coherent
    {X : Scheme.{u}} [IsNoetherian X]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [∀ U : X.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))]
    (E : schemeDerivedCategory X) (hE : IsPerfect X E)
    (G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ)
    (hGb : ∃ a b : ℤ, ∀ n : ℤ, n < a ∨ b < n → IsZero (G.X n))
    (hGcoherent : ∀ n : ℤ, RingedSpace.IsCoherent X.toRingedSpace (G.X n)) :
    (∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj
            (E ⊗ DerivedCategory.Q.obj G))) ∧
    (∀ i : ℤ, RingedSpace.IsCoherent X.toRingedSpace
      ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) i).obj
            (E ⊗ DerivedCategory.Q.obj G))) := by
  classical
  obtain ⟨c, d, hGbounds⟩ := hGb
  choose U hx K hK e using hE
  choose a b hKbounds using fun x ↦ (hK x).1
  have hlocal (x : X) (i : ℤ) :=
    strictPerfect_tensor_local_cohomology (U x) E (K x) (hK x) (e x).some
      G (a x) (b x) c d (hKbounds x) hGbounds hGcoherent i
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
    (fun x ↦ (U x : Set X)) (fun x ↦ (U x).isOpen) (by
      intro x _
      exact Set.mem_iUnion.mpr ⟨x, hx x⟩)
  let V : s → X.Opens := fun x ↦ U x.1
  have hcover : ⨆ x : s, V x = ⊤ := by
    apply eq_top_iff.mpr
    intro x _
    have hxcover := hs (Set.mem_univ x)
    simp only [Set.mem_iUnion, SetLike.mem_coe, exists_prop] at hxcover
    obtain ⟨y, hy, hxy⟩ := hxcover
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨y, hy⟩, hxy⟩
  let lower := insert 0 (s.image fun x ↦ a x + c)
  let upper := insert 0 (s.image fun x ↦ b x + d)
  have hlow : lower.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  have hupp : upper.Nonempty := ⟨0, Finset.mem_insert_self _ _⟩
  let lo := lower.min' hlow
  let hi := upper.max' hupp
  constructor
  · refine ⟨lo, hi, ?_⟩
    intro i hout
    apply Modules.isZero_of_iSup_eq_top _ V hcover
    intro x
    have hla : lo ≤ a x.1 + c := lower.min'_le _
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ x.2))
    have hbu : b x.1 + d ≤ hi := upper.le_max' _
      (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ x.2))
    apply (hlocal x.1 i).1
    rcases hout with hout | hout
    · exact Or.inl (hout.trans_le hla)
    · exact Or.inr (hbu.trans_lt hout)
  · intro i
    exact (coherent_module_local_on_open_cover X _ s V hcover).2
      (fun x ↦ (hlocal x.1 i).2)

end AlgebraicGeometry.Scheme
