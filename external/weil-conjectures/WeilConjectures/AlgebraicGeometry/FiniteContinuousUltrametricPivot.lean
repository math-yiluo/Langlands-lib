/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.MetricSpace.Ultra.Basic
public import Mathlib.Analysis.Normed.Field.Basic
public import Mathlib.Topology.ContinuousMap.Basic

import Mathlib.Analysis.Normed.Group.Ultra
import Mathlib.Data.Finset.Max

/-! # A local dominating member of a finite family of continuous functions -/

@[expose] public section

open scoped Topology

namespace ContinuousMap

/-- A finite family of continuous functions into an ultrametric normed field has a
nowhere-zero dominating member near any point where some member is nonzero.

Source: the continuous-function pivot argument in the integral coefficient application
of Bhatt--Scholze, Section 6.8. Choose a member with maximum norm at the point. Its norm
is positive. Intersect, over the finite family, the open loci where the difference from
its value at the point has norm below this maximum. The ultrametric inequality bounds
all functions by the maximum there, and the isosceles triangle identity keeps the
selected function's norm equal to the positive maximum.
(auxiliary; not a blueprint node) -/
theorem exists_open_dominating_member
    {S E I : Type*} [TopologicalSpace S] [NormedField E] [IsUltrametricDist E]
    [Finite I] (a : I → C(S, E)) (x : S) (hx : ∃ i, a i x ≠ 0) :
    ∃ (U : Set S) (i : I), IsOpen U ∧ x ∈ U ∧
      (∀ y ∈ U, a i y ≠ 0) ∧ ∀ j y, y ∈ U → ‖a j y‖ ≤ ‖a i y‖ := by
  classical
  let : Fintype I := Fintype.ofFinite I
  obtain ⟨i₀, hi₀⟩ := hx
  obtain ⟨i, _, hi⟩ := Finset.exists_max_image Finset.univ
    (fun j ↦ ‖a j x‖) ⟨i₀, Finset.mem_univ _⟩
  have hmax (j : I) : ‖a j x‖ ≤ ‖a i x‖ := hi j (Finset.mem_univ _)
  have hpos : 0 < ‖a i x‖ := (norm_pos_iff.mpr hi₀).trans_le (hmax i₀)
  let U : Set S := {y | ∀ j, ‖a j y - a j x‖ < ‖a i x‖}
  have hopen : IsOpen U := by
    simp only [U, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun j ↦
      isOpen_lt ((a j).continuous.sub continuous_const).norm continuous_const
  have hxU : x ∈ U := by
    intro j
    simpa only [sub_self, norm_zero] using hpos
  have hpivot (y : S) (hy : y ∈ U) : ‖a i y‖ = ‖a i x‖ := by
    have h : ‖a i y + -(a i x)‖ < max ‖a i y‖ ‖-(a i x)‖ := by
      simpa only [norm_neg, ← sub_eq_add_neg] using
        (hy i).trans_le (le_max_right ‖a i y‖ ‖a i x‖)
    simpa only [norm_neg] using IsUltrametricDist.norm_eq_of_add_norm_lt_max h
  refine ⟨U, i, hopen, hxU, ?_, ?_⟩
  · intro y hy
    exact norm_pos_iff.mp (by rw [hpivot y hy]; exact hpos)
  · intro j y hy
    rw [hpivot y hy]
    calc
      ‖a j y‖ = ‖(a j y - a j x) + a j x‖ := by rw [sub_add_cancel]
      _ ≤ max ‖a j y - a j x‖ ‖a j x‖ := IsUltrametricDist.norm_add_le_max _ _
      _ ≤ ‖a i x‖ := max_le (hy j).le (hmax j)

end ContinuousMap
