/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Topology.KrullDimension
import WeilConjectures.Mathlib.Topology.KrullDimension
public import Mathlib.AlgebraicGeometry.Properties

/-!
# A Noetherian scheme of dimension at most zero is finite and discrete

Source: Stacks Project, Properties, Lemma 28.10.5 (Tag 0AAX), proof and conclusion
(blueprint: lem-sc-zero-dim-noetherian-finite-discrete).
-/

@[expose] public section

set_option linter.style.haveILetI false


universe u

namespace AlgebraicGeometry

/-- A Noetherian scheme of topological Krull dimension at most zero has a finite discrete
underlying space: every point is closed and every singleton is open (`isClosed_discrete`,
`isOpen_discrete`). This includes the empty scheme.

Source: Stacks Project, Properties, Lemma 28.10.5 (Tag 0AAX), proof and conclusion
(blueprint: lem-sc-zero-dim-noetherian-finite-discrete).

Proof:
1. The underlying space is Noetherian by
   `lem-weil-pbc-noetherian-scheme-closed-subsets-minimal`. Local Noetherianity gives
   quasi-separatedness by `lem-weil-pbc-locally-noetherian-quasi-separated`, so
   `lem-weil-pbc-qcqs-scheme-spectral` gives spectrality (`def-weil-spectral-space`).
   It is therefore sober and T0: two distinct points with the same closure would be
   two generic points of the same irreducible closed subset, contradicting sobriety.
2. Apply `lem-sc-zero-dim-noetherian-closed-finite` to the whole closed space. The
   dimension bound gives finiteness and closedness of every singleton.
3. The complement of a singleton is a finite union of closed singletons, hence closed.
   Thus every singleton is open, so the space is discrete. For the empty scheme both
   singleton assertions are vacuous and its underlying type is finite.
-/
theorem finite_and_discreteTopology_of_topologicalKrullDim_le_zero
    (Y : Scheme.{u}) [IsLocallyNoetherian Y] [CompactSpace Y]
    (hdim : topologicalKrullDim Y ≤ 0) :
    Finite Y ∧ DiscreteTopology Y := by
  letI : IsNoetherian Y := {}
  letI : TopologicalSpace.NoetherianSpace Y := inferInstance
  letI : T0Space Y := inferInstance
  have h :=
    IsClosed.finite_and_isClosed_singleton_of_topologicalKrullDim_le_zero
      (X := Y) (Z := (Set.univ : Set Y)) isClosed_univ (by
        rw [IsHomeomorph.topologicalKrullDim_eq _ (Homeomorph.Set.univ Y).isHomeomorph]
        exact hdim)
  letI : Fintype (Set.univ : Set Y) := h.1.fintype
  have hfin : Finite Y := by
    exact Finite.of_injective
      (fun y : Y => (⟨y, Set.mem_univ y⟩ : (Set.univ : Set Y)))
      (fun x y e => by exact congrArg Subtype.val e)
  letI : Finite Y := hfin
  letI : T1Space Y := ⟨fun x => by simpa using h.2 x trivial⟩
  exact ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry
