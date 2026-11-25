/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.TensorPullback

/-! # The open where a module map is locally invertible

Source: Stacks Project, Tag 05GD, Lemma 10.79.4(3).
-/

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry.Scheme.Modules

/-- The union of the open subschemes on which the tensor pullback of a map is invertible.
This construction uses every such open, and makes no choice of frames or inverse.
Source: Stacks Project, Tag 05GD, Lemma 10.79.4(3).
(blueprint: def-sc-module-map-iso-locus) -/
noncomputable def moduleMapIsoLocus {W : Scheme.{u}} {M N : W.Modules} (φ : M ⟶ N) :
    W.Opens :=
  sSup {U : W.Opens | IsIso ((tensorPullback U.ι).map φ)}

/-- Membership means invertibility on an open neighbourhood.
(blueprint: def-sc-module-map-iso-locus)
-/
theorem mem_moduleMapIsoLocus {W : Scheme.{u}} {M N : W.Modules} (φ : M ⟶ N) (x : W) :
    x ∈ moduleMapIsoLocus φ ↔
      ∃ U : W.Opens, IsIso ((tensorPullback U.ι).map φ) ∧ x ∈ U := by
  exact TopologicalSpace.Opens.mem_sSup

end AlgebraicGeometry.Scheme.Modules
