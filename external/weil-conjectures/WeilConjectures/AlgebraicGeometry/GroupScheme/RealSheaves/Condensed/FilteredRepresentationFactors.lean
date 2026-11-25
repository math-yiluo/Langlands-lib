/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.RepresentationTheory.Filtration

/-!
# Composition factors of prescribed graded pieces

Refinement and Jordan–Hölder, as used in paragraph 3 of
`lemma-tensor-exterior-powers-filtered-representations--3`.
-/

@[expose] public section

set_option autoImplicit false

namespace RealSheaves.Condensed

universe u v w z

/-- Refine each graded piece by a composition series, then compare the resulting composition
series with the prescribed series by Jordan–Hölder. The refinement indices are pairs consisting
of a graded-piece index and a factor index, so multiplicities are retained, including empty
series for zero pieces.
Source: `lemma-tensor-exterior-powers-filtered-representations--3`, proof paragraph 3,
filtration-refinement step (blueprint: lem-mg-filtered-representation-factors).
-/
theorem filteredRepresentationFactors
    {k : Type u} [Field k] {W : Type w} [Group W]
    {V : Type v} [AddCommGroup V] [Module k V]
    {ρ : Representation k W V} {ι : Type z} {X : ι → Type v}
    [∀ i, AddCommGroup (X i)] [∀ i, Module k (X i)]
    (τ : ∀ i, Representation k W (X i))
    (h : Representation.HasGradedPieces ρ (fun i ↦ Representation.EquivTo (τ i)))
    (t : ∀ i, (τ i).CompositionSeries) (c : ρ.CompositionSeries) :
    ∃ e : Fin c.length ≃ Σ i, Fin (t i).length,
      (∀ j, Nonempty ((c.factor j).Equiv ((t (e j).1).factor (e j).2))) ∧
      ∀ i j, Nonempty ((c.factor (e.symm ⟨i, j⟩)).Equiv ((t i).factor j)) := by
  have hr := h.trans
    (R := fun i j ↦ Representation.EquivTo ((t i).factor j))
    (fun _ _ ↦ Representation.isInvariant_equivTo _)
    (fun i {_} {_} {_} _ hi ↦ (t i).hasGradedPieces.of_equiv
      (fun _ ↦ Representation.isInvariant_equivTo _) hi.equiv.symm)
  obtain ⟨e, he⟩ := Representation.CompositionSeries.exists_equiv_of_hasGradedPieces hr
    (fun _ ↦ Representation.isInvariant_equivTo _)
    (fun x {_} {_} {_} _ hx ↦ hx.some.isIrreducible_iff.2
      ((t x.1).isIrreducible_factor x.2)) c
  refine ⟨e, he, fun i j ↦ ?_⟩
  have h := he (e.symm ⟨i, j⟩)
  rw [e.apply_symm_apply] at h
  exact h

end RealSheaves.Condensed
