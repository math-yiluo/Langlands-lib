# Uniformizer-power multiples lie in the corresponding ideal power (M133.023)

`Langlands.NYLL.LocalFieldTheory.mul_uniformizer_pow_mem_maximalIdeal_pow` proves the exact published target
`Langlands.NYLL.LocalFieldTheory.mul_uniformizer_pow_mem_maximalIdeal_powStatement` applied to all its parameters in source order.
The field universe is arbitrary; the theorem retains the field, valuative
relation, topology and nonarchimedean local-field instances, together with
every explicit element and proof hypothesis of its target.

Rewrite the maximal ideal as the principal ideal of the irreducible
uniformizer, then rewrite its `n`th power as the principal ideal of
`ϖ ^ n`. Membership in a singleton span is divisibility. The witness is
`r`, with multiplication commuted to match the divisibility convention.

The original is Naganori Yamaguchi's
`LocalFieldTheory.mul_uniformizer_pow_mem_maximalIdeal_pow`, source unit M133.023,
lines 363–370 (target) and 346–350 (inlined prerequisite) of
`Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`. The registered readable source
`external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The source file SHA-256 is
`8c7082cb0e2e8ac6db22ff1afd4a1d173032246eac681ed075bb9feab7c5f71e`.
The attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
No applicable NYLL erratum was found in the published errata directory.

Worker 212 extracted this proof into the required module, added the
`Langlands.NYLL` namespace prefix, reduced imports to the exact target module
and any explicitly listed proof dependencies, and wrote the theorem type as
the exact named Prop target. The source invokes M133.021 before the divisibility step. That proof is not
yet published, so its two Mathlib rewrites are performed directly here.
The remaining proof is unchanged after unfolding the named Prop target.
Only the published statement module is imported; there is no local or public
duplicate of the M133.021 declaration.
No new axiom or alternate public theorem name is introduced.

The original copyright and author header is retained verbatim:
copyright 2026 Naganori Yamaguchi, all rights reserved; authors Naganori
Yamaguchi (assisted by OpenAI Codex); Apache-2.0. The original
[LICENSE](../../../../../../../licenses/NYLL/LICENSE), SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`, and
[NOTICE](../../../../../../../licenses/NYLL/NOTICE), SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`,
remain unchanged in `licenses/NYLL/`. This extraction uses the pinned
source directly and reuses no other worker's private draft or compatibility
patch. Its conclusion is the specified local-field support proposition.
