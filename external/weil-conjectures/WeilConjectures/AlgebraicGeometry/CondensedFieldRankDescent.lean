/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.Topology.LocallyConstant.Basic
public import Mathlib.Topology.NoetherianSpace

import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# Locally constant ranks descended through flat covers

Source: the rank/descent argument, steps 4--5, accompanying Hemo--Richarz--Scholbach,
Example 3.1 (auxiliary; not a blueprint node).
-/

@[expose] public section

universe u v

open CategoryTheory Limits TopologicalSpace
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

private lemma closed_of_specializes_iff {Y : Type*} [TopologicalSpace Y]
    [NoetherianSpace Y] [QuasiSober Y] {S : Set Y}
    (hS : ∀ ⦃x y : Y⦄, x ⤳ y → (x ∈ S ↔ y ∈ S)) : IsClosed S := by
  have hfin := NoetherianSpace.finite_irreducibleComponents (α := Y)
  have : S = ⋃ C ∈ {C ∈ irreducibleComponents Y | (C ∩ S).Nonempty}, C := by
    ext y
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · intro hy
      exact ⟨irreducibleComponent y, ⟨irreducibleComponent_mem_irreducibleComponents y, y,
        mem_irreducibleComponent, hy⟩, mem_irreducibleComponent⟩
    · rintro ⟨C, ⟨hC, x, hxC, hxS⟩, hyC⟩
      obtain ⟨η, hη⟩ := QuasiSober.sober (hC.1 : IsIrreducible C)
        (isClosed_of_mem_irreducibleComponents C hC)
      exact (hS (hη.specializes hyC)).1 ((hS (hη.specializes hxC)).2 hxS)
  rw [this]
  exact (hfin.subset fun C hC ↦ hC.1).isClosed_biUnion fun C hC ↦
    isClosed_of_mem_irreducibleComponents C hC.1

/-- Fibre-compatible specialization-invariant functions on a flat cover have locally
constant descent on a topologically noetherian scheme.
Source: the rank/descent argument, steps 4--5, accompanying Hemo--Richarz--Scholbach,
Example 3.1 (auxiliary; not a blueprint node).
Proof: choose a lift of each base point. Fibre compatibility identifies every other
lift's value. Flat going-down lifts a generalization through the chosen lift, so the
base function is invariant under specialization. Each fibre is a union of the finitely
many closed irreducible components, using their generic points; so is its complement.
Thus each fibre is open. The argument also covers an empty base or empty cover. -/
theorem exists_locallyConstant_descent_of_specializes
    {X : Scheme.{u}} [NoetherianSpace X] {I : Type v} (V : I → Scheme.{u})
    (f : ∀ i, V i ⟶ X) (hf : ∀ i, Flat (f i))
    (hsurj : ∀ x : X, ∃ i, ∃ v : V i, f i v = x)
    {A : Type*} (r : ∀ i, V i → A)
    (hcompat : ∀ i j (v : V i) (w : V j), f i v = f j w → r i v = r j w)
    (hspec : ∀ i ⦃v w : V i⦄, v ⤳ w → r i v = r i w) :
    ∃ d : X → A, IsLocallyConstant d ∧ ∀ i v, d (f i v) = r i v := by
  classical
  choose k v hv using hsurj
  let d (x : X) := r (k x) (v x)
  have hd (i) (w : V i) : d (f i w) = r i w :=
    hcompat _ _ _ _ (hv _)
  have hdspec {x y : X} (h : x ⤳ y) : d x = d y := by
    let _ := hf (k y)
    have hg : GeneralizingMap (f (k y)) := Flat.generalizingMap _
    obtain ⟨w, hw, hfw⟩ := hg (show x ⤳ f (k y) (v y) by rw [hv]; exact h)
    rw [← hfw, hd]
    exact hspec _ hw
  refine ⟨d, (IsLocallyConstant.iff_isOpen_fiber).2 (fun a ↦ ?_), hd⟩
  apply isClosed_compl_iff.mp
  apply closed_of_specializes_iff
  intro x y h
  change (¬ d x = a) ↔ (¬ d y = a)
  rw [hdspec h]

end AlgebraicGeometry.ProEtale
