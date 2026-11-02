/-
Ported from `Theorems/Thm_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range.lean` of the Anthropic Lean formalization of
Fermat's Last Theorem (commit 6e837e75355538c7f80bab5b956861e86c4eacc2), Copyright 2026
Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.
Modified: FLT module names are prefixed by `Langlands.AnthropicFLT`; the FLT lakefile options
are set after the imports; the import of `P2M.Util` is dropped; the proof `by
p2m_exact_reverting @_root_.S.solution` is replaced by the term `S.solution` applied to the
explicit arguments. The paired Markdown file lists the changes.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem Algebra.TensorProduct.isField_of_isSeparable_of_forall_isSeparable_mem_range
    (k : Type u) (F : Type v) (K : Type w) [Field k] [Field F] [Field K] [Algebra k F]
    [Algebra k K] [Algebra.IsSeparable k K]
    (hsc : ∀ y : F, IsSeparable k y → y ∈ (algebraMap k F).range) :
    IsField (F ⊗[k] K) :=
  P2MW.S_Algebra_TensorProduct_isField_of_isSeparable_of_forall_isSeparable_mem_range.solution k F K hsc
