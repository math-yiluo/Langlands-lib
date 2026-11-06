# `Langlands.AnthropicFLT.P2M.Sol.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow`

Ported for task `20cb772c-aef4-4734-b435-db22f8ee9032` (proper coherent formal existence over complete local noetherian rings). Proof module (FLT `P2M/Sol/`).

## Source and licence

Port of `P2M/Sol/S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.lean` from the Anthropic Lean formalisation of Fermat's Last Theorem (commit `6e837e75355538c7f80bab5b956861e86c4eacc2`; project literature folder "Anthropic - Fermat's Last Theorem - complete Lean source at 6e837e75355538c7f80bab5b956861e86c4eacc2", literature id `anthropic-flt-complete-lean-source-6e837e75`). The text is the FLT text except for the changes listed below.

Licence: Apache License, Version 2.0; Copyright 2026 Anthropic, PBC. Copies of the FLT `LICENSE`, `NOTICE` and `ATTRIBUTION.md` are in `licenses/Anthropic-FLT/` (added by statement artifact `a25bcdd5-03da-45b4-a0d3-100bb603e7c5`).

FLT `ATTRIBUTION.md` does not list this file as containing third-party material.

## Changes against the FLT file

- The FLT lakefile options are inserted after the imports: `maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`.
- An attribution header comment is added at the top of the file.
- The import of the FLT utility module `P2M.Util` (custom tactics and commands) is dropped.
- Each FLT command `p2m_export "N" "a b …"` (from `P2M.Util`; it adds the aliases `a`, `b`, … in the current namespace for `N.a`, `N.b`, …) is replaced by the Lean command `export _root_.N (a b …)`, which adds the same aliases.
- Each FLT command `p2m_open "N₁ N₂ …"` (from `P2M.Util`; it opens the namespaces with their exact names, `N~x~y` hiding `x` and `y`) is replaced by `open _root_.N₁ _root_.N₂ …`, and `N~x~y` by `open _root_.N hiding x y`.
- `p2m_open` also opens namespaces of this module before they exist (later commands create them): `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion`. Lean's `open` rejects a namespace that does not exist yet, so each of them is registered by an empty block `namespace N end N` right after the options; the `open` then has the FLT effect.
- No other change: the declarations, statements and proofs are the FLT text.

## Content

The theorem `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.solution`
proves the statement of the companion theorem in
`Langlands.AnthropicFLT.Theorems.Thm_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow`.

Proof (namespace `AdicCompletion.AssemblyProof` inside the solution namespace). `factorPow_evalₐ`: the
evaluations of the completion are compatible with the projections `R ⧸ I^n → R ⧸ I^m`. Section `Levelwise`:
the hypotheses make `R → S ⧸ J^k` surjective with kernel `I^k`, so it induces ring isomorphisms
`ψ k : R ⧸ I^k → S ⧸ J^k` (`ψ_mk`, `ψ_injective`, `ψ_surjective`, `e`) compatible with the projections
(`factorPow_comp_ψ`). The maps `ψ n ∘ evalₐ` and `(e n)⁻¹ ∘ evalₐ` are compatible families, so
`AdicCompletion.liftRingHom` gives ring maps `F` and `G` between the completions (`evalₐ_F`, `evalₐ_G`), which
are mutually inverse (`F_comp_G`, `G_comp_F`; checked on all evaluations with `AdicCompletion.ext_evalₐ`).
`solution` takes `e := RingEquiv.ofRingHom F G` and checks `F (r) = f r` in the completion of `S` on every
evaluation (`ψ_mk`).

## Declarations

Names, namespaces and statements are the FLT ones. Solution modules put their auxiliary declarations in the FLT namespace `P2MW.<module name>`.

- theorem `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.AssemblyProof.factorPow_evalₐ`
- def `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.AssemblyProof.ψ`
- theorem `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.AssemblyProof.ψ_mk`
- theorem `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.AssemblyProof.ψ_injective`
- theorem `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.AssemblyProof.factorPow_comp_ψ`
- theorem `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.AssemblyProof.ψ_surjective`
- def `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.AssemblyProof.e`
- theorem `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.AssemblyProof.e_apply`
- theorem `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.AssemblyProof.compatF`
- def `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.AssemblyProof.F`
- theorem `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.AssemblyProof.evalₐ_F`
- theorem `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.AssemblyProof.compatG`
- def `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.AssemblyProof.G`
- theorem `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.AssemblyProof.evalₐ_G`
- theorem `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.AssemblyProof.F_comp_G`
- theorem `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.AssemblyProof.G_comp_F`
- theorem `P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.P2MW.S_AdicCompletion_exists_ringEquiv_of_forall_quotient_mk_comp_surjective_of_forall_ker_eq_pow.AdicCompletion.solution`

## Dependencies

Ported FLT modules imported: none.
Other imports: `Mathlib`.
