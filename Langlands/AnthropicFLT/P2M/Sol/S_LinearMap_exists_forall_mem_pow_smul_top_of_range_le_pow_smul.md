# `Langlands.AnthropicFLT.P2M.Sol.S_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul`

Ported for the proof of proper coherent formal existence over complete local noetherian rings, `Langlands.AlgebraicGeometry.Modules.properFormalCoherentExistence`, which depends on this module through its imports. Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/`.

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul.solution` proves the statement of
the companion theorem in `Langlands.AnthropicFLT.Theorems.Thm_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul`.

Proof. `HomARSol.pi_mem_smul_top`: a tuple whose entries lie in `J • N` lies in `J • N^r`. `solution`: choose
generators `gen_1, …, gen_r` of `M`; evaluation `ev : Hom(M, N) → N^r`, `g ↦ (g (gen i))_i`, is injective. Mathlib's
Artin–Rees lemma `Ideal.exists_pow_inf_eq_pow_smul` for the submodule `range ev ⊆ N^r` gives `k` with
`I^m N^r ∩ range ev = I^(m−k) (I^k N^r ∩ range ev)` for `m ≥ k`. If `range g ⊆ I^(n+k) N`, then
`ev g ∈ I^(n+k) N^r ∩ range ev ⊆ I^n • range ev = ev (I^n • Hom(M, N))`, and injectivity of `ev` gives
`g ∈ I^n • Hom(M, N)`. The constant is `c = k`.

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul.HomARSol.pi_mem_smul_top`
- theorem `P2MW.S_LinearMap_exists_forall_mem_pow_smul_top_of_range_le_pow_smul.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
