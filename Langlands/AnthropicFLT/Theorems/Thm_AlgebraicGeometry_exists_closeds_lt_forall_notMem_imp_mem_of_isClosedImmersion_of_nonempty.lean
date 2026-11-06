/-
Ported from `Theorems/Thm_AlgebraicGeometry_exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options are set after the imports; the import of `P2M.Util` is dropped; the proof `by p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] (T : Closeds X) (hT : Set.range i.base = (T : Set X))
    (U : Z.Opens) (hU : (U : Set Z).Nonempty) :
    ∃ T' : Closeds X, T' < T ∧ ∀ z : Z, z ∉ U → i.base z ∈ T' :=
  P2MW.S_AlgebraicGeometry_exists_closeds_lt_forall_notMem_imp_mem_of_isClosedImmersion_of_nonempty.solution i T hT U hU
