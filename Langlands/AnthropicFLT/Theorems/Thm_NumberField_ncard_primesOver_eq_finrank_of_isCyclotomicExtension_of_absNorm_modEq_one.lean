/-
Ported from
`Theorems/Thm_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.lean`
(entire file, 16 lines) of the Anthropic Lean formalization of Fermat's Last Theorem: registered
source `anthropic-flt-complete-lean-source-6e837e75`, commit
6e837e75355538c7f80bab5b956861e86c4eacc2, original file SHA256
e69890e27cae1f08c39b27c271ca570d143cb61016c14a47f3d7fede2bb404bd.
Copyright 2026 Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.

Complete list of edits to the source text (the paired Markdown file gives the same list; the audit
`notes/reuse/anthropic-chebotarev-audit.md` and its evidence files `compatibility.md`,
`universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact
diffs):
- Imports of FLT modules use the `Langlands.AnthropicFLT` prefix.
- The source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set
  after the imports.
- The audit's modification comments are replaced by the port header.
- The import of `P2M.Util` is dropped.
- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`; the
  binder of `L` (originally `Type`) is `Type v`. The audit named these universes `audit_u`,
  `audit_v`, `audit_w`.
- Cleanup: the line `attribute [-instance] Deep.NTSupply.instNormalRayClassSubgroup` was removed;
  the proof `by p2m_exact_reverting
  @_root_.P2MW.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.solution`
  was replaced by `apply
  @_root_.P2MW.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.solution
  (m := m) <;> assumption`, where the modulus m is passed explicitly.

Declaration names and namespaces are unchanged. Apart from the universe generalization, the
mathematical hypotheses and conclusions of the source are retained.
-/
import Mathlib
import Langlands.AnthropicFLT.P2M.Sol.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

set_option autoImplicit false

open NumberField

theorem NumberField.ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one
    (K : Type u) (L : Type v) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (m : ℕ) [NeZero m] [IsCyclotomicExtension {m} K L]
    (v : Ideal (𝓞 K)) [v.IsMaximal] (hcop : (Ideal.absNorm v).Coprime m)
    (h1 : (Ideal.absNorm v : ZMod m) = 1) :
    (v.primesOver (𝓞 L)).ncard = Module.finrank K L ∧
      ∀ w : Ideal (𝓞 L), w ∈ v.primesOver (𝓞 L) → Ideal.absNorm w = Ideal.absNorm v := by
  apply @_root_.P2MW.S_NumberField_ncard_primesOver_eq_finrank_of_isCyclotomicExtension_of_absNorm_modEq_one.solution (m := m) <;> assumption
