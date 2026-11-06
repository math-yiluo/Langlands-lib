# `Langlands.AnthropicFLT.P2M.Sol.S_IsAdicComplete_of_module_finite`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_IsAdicComplete_of_module_finite.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_IsAdicComplete_of_module_finite.solution` proves the statement of the companion theorem
in `Langlands.AnthropicFLT.Theorems.Thm_IsAdicComplete_of_module_finite`; it is
`M4cP1X1.isAdicComplete_of_module_finite`.

Proof (namespace `M4cP1X1`). Section `Compare`: if `I ≤ J` and `J^N ≤ I`, the `I`-adic and `J`-adic
topologies agree, so Hausdorffness, precompleteness and completeness transfer
(`smul_top_pow_le_of_le`, `smul_top_pow_mul_le_of_pow_le`, `isHausdorff_of_le`, `isHausdorff_of_pow_le`,
`isPrecomplete_of_le_of_pow_le`, `isPrecomplete_of_pow_le_of_le`, `isAdicComplete_iff_of_le_of_pow_le`).
Section `ModuleFinite`: precompleteness passes to quotients (`isPrecomplete_of_surjective`, via surjectivity
of `of I M` and of the induced map on completions) and to `ι → R` (`isPrecomplete_pi`), hence to finite modules
(`isPrecomplete_of_module_finite`); over a noetherian ring with `I` in the Jacobson radical (true for a complete
ring), finite modules are `I`-adically Hausdorff (Krull, `IsHausdorff.of_le_jacobson`), which gives
`isAdicComplete_of_module_finite`. Section `Local` (not used by `solution`): for a finite local algebra `T`
over a local ring `𝒪` with local structure map, some power of the maximal ideal of `T` lies in `m_𝒪 T`
(`exists_maximalIdeal_pow_le_map`), so `T` is complete for its maximal ideal when `𝒪` is complete and
noetherian (`isAdicComplete_maximalIdeal_of_module_finite`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_IsAdicComplete_of_module_finite.M4cP1X1.smul_top_pow_le_of_le`
- theorem `P2MW.S_IsAdicComplete_of_module_finite.M4cP1X1.smul_top_pow_mul_le_of_pow_le`
- theorem `P2MW.S_IsAdicComplete_of_module_finite.M4cP1X1.isHausdorff_of_le`
- theorem `P2MW.S_IsAdicComplete_of_module_finite.M4cP1X1.isHausdorff_of_pow_le`
- theorem `P2MW.S_IsAdicComplete_of_module_finite.M4cP1X1.isPrecomplete_of_le_of_pow_le`
- theorem `P2MW.S_IsAdicComplete_of_module_finite.M4cP1X1.isPrecomplete_of_pow_le_of_le`
- theorem `P2MW.S_IsAdicComplete_of_module_finite.M4cP1X1.isAdicComplete_iff_of_le_of_pow_le`
- theorem `P2MW.S_IsAdicComplete_of_module_finite.M4cP1X1.isPrecomplete_of_surjective`
- theorem `P2MW.S_IsAdicComplete_of_module_finite.M4cP1X1.isPrecomplete_pi`
- theorem `P2MW.S_IsAdicComplete_of_module_finite.M4cP1X1.isPrecomplete_of_module_finite`
- theorem `P2MW.S_IsAdicComplete_of_module_finite.M4cP1X1.isAdicComplete_of_module_finite`
- theorem `P2MW.S_IsAdicComplete_of_module_finite.M4cP1X1.exists_maximalIdeal_pow_le_map`
- theorem `P2MW.S_IsAdicComplete_of_module_finite.M4cP1X1.isAdicComplete_maximalIdeal_of_module_finite`
- theorem `P2MW.S_IsAdicComplete_of_module_finite.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib.RingTheory.AdicCompletion.Functoriality`, `Mathlib.RingTheory.AdicCompletion.Exactness`, `Mathlib.RingTheory.AdicCompletion.Noetherian`, `Mathlib.RingTheory.Finiteness.Cardinality`, `Mathlib.RingTheory.LocalRing.Quotient`, `Mathlib.RingTheory.LocalRing.RingHom.Basic`, `Mathlib.RingTheory.Artinian.Module`, `Mathlib.RingTheory.Ideal.Over`.
