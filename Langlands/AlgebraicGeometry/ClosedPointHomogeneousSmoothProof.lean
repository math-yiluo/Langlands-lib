/-
Copyright (c) 2026 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Adapted from Mathlib's group-scheme smoothness proof by Worker 137.
-/
import Langlands.AlgebraicGeometry.ClosedPointHomogeneousSmoothStatement

/-! # Proof of smoothness from transitivity on closed points -/

open CategoryTheory AlgebraicGeometry

universe u

namespace Langlands.AlgebraicGeometry

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem closedPointHomogeneousSmooth :
    ClosedPointHomogeneousSmoothStatement.{u} := by
  intro K _ _ X f _ _ htrans
  have := LocallyOfFiniteType.jacobsonSpace f
  rw [← Scheme.Hom.smoothLocus_eq_top_iff, ← TopologicalSpace.Opens.coe_eq_univ,
    ← not_ne_iff, ← Set.nonempty_compl]
  intro H
  obtain ⟨x, hx, hxc⟩ :=
    nonempty_inter_closedPoints H f.smoothLocus.2.isClosed_compl.isLocallyClosed
  have : Nonempty X := ⟨x⟩
  obtain ⟨y, hy : y ∈ f.smoothLocus, hyc⟩ := nonempty_inter_closedPoints
    f.dense_smoothLocus_of_perfectField.nonempty f.smoothLocus.2.isLocallyClosed
  obtain ⟨α, hα, hαxy⟩ := htrans x y hxc hyc
  rw! [← hαxy, ← α.hom.mem_preimage, Scheme.Hom.preimage_smoothLocus_eq, hα] at hy
  exact hx hy

end Langlands.AlgebraicGeometry
