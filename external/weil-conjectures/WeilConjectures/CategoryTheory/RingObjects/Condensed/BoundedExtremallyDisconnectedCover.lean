/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Category.Profinite.Basic
public import Mathlib.Topology.ExtremallyDisconnected
public import Mathlib.SetTheory.Cardinal.Basic

import Mathlib.Topology.Category.Stonean.Basic

/-!
# Bounded extremally disconnected covers of profinite spaces

Source: Stacks Project, Topology, Tags 090D and 090E
(blueprint: lem-weil-pbc-bounded-extremally-disconnected-cover).
-/

@[expose] public section

universe u

namespace Profinite

/-- Every profinite space admits an extremally disconnected profinite cover with the stated
cardinal bound. Source: Stacks Project, Topology, Tags 090D and 090E
(blueprint: lem-weil-pbc-bounded-extremally-disconnected-cover).

Proof plan:
1. Take the ultrafilters on the underlying set of `X`, with the compact Hausdorff topology
and clopen membership basis of `lem-weil-pbc-ultrafilter-compact-hausdorff-basis`.
The principal ultrafilter at `s` belongs to the basic set `[A]` exactly when `s ∈ A`.
2. Extend the identity set map to `X` by `lem-weil-pbc-ultrafilter-continuous-extension`.
The extension is continuous and sends the principal ultrafilter at `s` to `s`, hence is onto.
3. For an open set `O`, put `A = {s | pure s ∈ O}`. The membership basis gives `O ⊆ [A]`.
Every basic neighbourhood of a point of `[A]` contains a principal ultrafilter in `O`,
since the intersection of its defining set with `A` belongs to a proper ultrafilter.
Thus the closure of `O` is `[A]`, which is open, proving extremal disconnectedness.
4. Distinct ultrafilters are separated by a clopen membership set. Therefore any connected
subset has at most one point, proving total disconnectedness and hence profiniteness.
5. An ultrafilter is a family of subsets, so the underlying set embeds in the double power
set of `X`. An injection of `X` into a set of cardinal `κ` induces injections of power sets
and then double power sets, yielding the bound `2 ^ (2 ^ κ)`. For empty `X` there are no
ultrafilters, and the same construction and estimate apply. -/
theorem exists_bounded_extremallyDisconnected_cover (X : Profinite.{u}) (κ : Cardinal.{u})
    (hκ : Cardinal.aleph0 ≤ κ) (hX : Cardinal.mk X ≤ κ) :
    ∃ (T : Profinite.{u}) (u : ContinuousMap T X),
      Function.Surjective u ∧ ExtremallyDisconnected T ∧
        Cardinal.mk T ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ) := by
  classical
  -- The construction also works for finite bounds; retain the stated hypothesis.
  have _ := hκ
  let P := X.presentation
  let f : ContinuousMap (Stonean.toProfinite.obj P) X :=
    CategoryTheory.ConcreteCategory.hom (Profinite.presentation.π X)
  refine ⟨Stonean.toProfinite.obj P, f, ?_, ?_, ?_⟩
  · have h : CategoryTheory.Epi (Profinite.presentation.π X) := inferInstance
    rw [Profinite.epi_iff_surjective] at h
    exact h
  · exact P.prop
  · change Cardinal.mk (Ultrafilter X) ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ)
    let g : Ultrafilter X → Set (Set X) := fun F ↦ (F : Filter (X : Type u)).sets
    have hg : Function.Injective g := by
      intro F G hFG
      apply Ultrafilter.ext
      intro A
      simpa [g] using Set.ext_iff.mp hFG A
    calc
      Cardinal.mk (Ultrafilter X) ≤ Cardinal.mk (Set (Set X)) :=
        Cardinal.mk_le_of_injective hg
      _ = (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ Cardinal.mk X) := by
        rw [Cardinal.mk_set, Cardinal.mk_set]
      _ ≤ (2 : Cardinal.{u}) ^ ((2 : Cardinal.{u}) ^ κ) := by
        apply Cardinal.power_le_power_left two_ne_zero
        apply Cardinal.power_le_power_left two_ne_zero
        exact hX

end Profinite
