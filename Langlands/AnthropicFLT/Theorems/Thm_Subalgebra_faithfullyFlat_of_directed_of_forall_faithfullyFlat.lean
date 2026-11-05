/-
Ported from `Theorems/Thm_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat.lean` of the Anthropic FLT formalization,
commit 6e837e75355538c7f80bab5b956861e86c4eacc2. Copyright 2026 Anthropic, PBC.
Licensed under Apache License 2.0; see licenses/Anthropic-FLT/LICENSE, NOTICE,
and ATTRIBUTION.md. Imports are prefixed; utility commands are replaced by
standard Lean commands. See the paired Markdown for changes and provenance.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open scoped TensorProduct

universe u v w

theorem Subalgebra.faithfullyFlat_of_directed_of_forall_faithfullyFlat
    {k : Type u} [Field k] {H : Type v} [CommRing H] [Algebra k H] (K : Subalgebra k H)
    {ι : Type w} [Nonempty ι] (F : ι → Subalgebra k H) (hdir : Directed (· ≤ ·) F)
    (hle : ∀ i, F i ≤ K) (hcov : ∀ x ∈ K, ∃ i, x ∈ F i)
    (hff : ∀ i, Module.FaithfullyFlat ↥(F i) H) :
    Module.FaithfullyFlat ↥K H := by
  exact _root_.P2MW.S_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat.solution K F hdir hle hcov hff
