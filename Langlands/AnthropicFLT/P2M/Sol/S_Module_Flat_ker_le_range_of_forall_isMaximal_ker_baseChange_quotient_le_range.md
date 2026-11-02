# `Langlands.AnthropicFLT.P2M.Sol.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- 1 `p2m_reactivate "N₁ N₂ …"` command(s) (an FLT command from `P2M.Util` that re-activates the scoped extensions, such as scoped instances and simp lemmas, of the named namespaces) are replaced by `open scoped _root_.N₁ _root_.N₂ …` with the same namespaces, which activates the same scoped extensions.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range`. Statement. `Module.Flat.ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range`: over a noetherian ring, a bounded
complex of flat modules with finitely generated cohomology is exact in positive degrees if all its reductions modulo
maximal ideals are.

Proof. Descending induction on the degree (section `Trunc`). The top cohomology is finitely generated and vanishes
modulo every maximal ideal, hence vanishes by Nakayama (`subsingleton_of_forall_isMaximal`,
`surjective_of_forall_isMaximal`). Then the top differential is surjective, its kernel is flat (ported
`Module.Flat.ker_of_surjective_of_flat`) and the truncated complex `T` (`dT`, `flatT`) again satisfies the hypotheses,
the reductions being compatible by the ported `Module.Flat.ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact`
(`subtype_baseChange`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range.CoreNak17.subsingleton_of_forall_isMaximal`
- theorem `P2MW.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range.CoreNak17.surjective_of_forall_isMaximal`
- def `P2MW.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range.CoreNak17.T`
- scoped instance `P2MW.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range.CoreNak17.instTacg`
- scoped instance `P2MW.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range.CoreNak17.instTmod`
- def `P2MW.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range.CoreNak17.dT`
- theorem `P2MW.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range.CoreNak17.flatT`
- theorem `P2MW.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range.CoreNak17.subtype_baseChange`
- theorem `P2MW.S_Module_Flat_ker_le_range_of_forall_isMaximal_ker_baseChange_quotient_le_range.solution`

## Dependencies

Ported FLT modules imported: `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_ker_of_surjective_of_flat` (Library), `Langlands.AnthropicFLT.Theorems.Thm_Module_Flat_ker_baseChange_eq_bot_and_ker_le_range_of_flat_of_exact` (Library).
Other imports: `Mathlib`.
