# `Langlands.AnthropicFLT.P2M.Sol.S_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top.solution` proves the statement of
the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top`.

Proof (namespace `P2mWs3Glue`): the standard clearing-of-denominators gluing argument. Multiplication by `r^n` is
injective on a localization at `r` (`smul_pow_injective`). A finite family `x i ∈ M_{g_i}` has common numerators:
`g_i^a • x i = f i (m i)` for one exponent `a` (`exists_common_numerators`). `exists_of_compatible`: compatibility
on the overlaps `N₂ i j` (localizations of `N i` at `g j`) gives, after multiplying by a further power,
`g_j^b g_i^a m_i = g_i^b g_j^a m_j` in `M`; writing `1 = ∑_i c_i g_i^(a+b)` (since the `g_i` generate the unit
ideal), the element `m = ∑_i c_i g_i^b m_i` satisfies `f i m = x i` for every `i`. `solution` is
`P2mWs3Glue.exists_of_compatible`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top.P2mWs3Glue.smul_pow_injective`
- theorem `P2MW.S_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top.P2mWs3Glue.exists_common_numerators`
- theorem `P2MW.S_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top.P2mWs3Glue.exists_of_compatible`
- theorem `P2MW.S_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
