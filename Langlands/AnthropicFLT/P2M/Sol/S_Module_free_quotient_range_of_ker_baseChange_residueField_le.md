# `Langlands.AnthropicFLT.P2M.Sol.S_Module_free_quotient_range_of_ker_baseChange_residueField_le`

Ported for task `6d6cc279-3071-445f-adba-589e54d9816b` (projective representability of the relative endomorphism functor of a projective abelian scheme). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_Module_free_quotient_range_of_ker_baseChange_residueField_le.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- Imports of FLT modules (`Definitions.*`, `Theorems.*`, `P2M.*`) are renamed to `Langlands.AnthropicFLT.*`; Mathlib imports are unchanged.
- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_Module_free_quotient_range_of_ker_baseChange_residueField_le.solution` proves the statement of the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_Module_free_quotient_range_of_ker_baseChange_residueField_le`. Statement. `Module.free_quotient_range_of_ker_baseChange_residueField_le`: over a local ring `R`, let `f : M → N` with `M`
finite and `N` finite free. If every element of the kernel of `f ⊗ κ` comes from `(ker f) ⊗ κ`, then `N / im f` is
free.

Proof. The hypothesis says that `(im f) ⊗ κ → N ⊗ κ` is injective (local `rangeRestrict_comp_ker_subtype`,
`subtype_comp_rangeRestrict`, `lTensor_subtype_range_injective`). Lifting a basis of `(im f) ⊗ κ` and extending it
to a basis of the free module `N ⊗ κ`, Nakayama's lemma shows that `im f` is a direct summand of `N` with free
complement (`free_quotient_range`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_Module_free_quotient_range_of_ker_baseChange_residueField_le.P2mKcTorCrit.rangeRestrict_comp_ker_subtype`
- theorem `P2MW.S_Module_free_quotient_range_of_ker_baseChange_residueField_le.P2mKcTorCrit.subtype_comp_rangeRestrict`
- theorem `P2MW.S_Module_free_quotient_range_of_ker_baseChange_residueField_le.P2mKcTorCrit.lTensor_subtype_range_injective`
- theorem `P2MW.S_Module_free_quotient_range_of_ker_baseChange_residueField_le.P2mKcTorCrit.free_quotient_range`
- theorem `P2MW.S_Module_free_quotient_range_of_ker_baseChange_residueField_le.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
