# A chosen uniformizer power clears an integer-ring denominator (M133.020)

`Langlands.NYLL.LocalFieldTheory.exists_chosenIntegerRingUniformizer_pow_mul_mem_integerRing` proves the exact published target
`Langlands.NYLL.LocalFieldTheory.exists_chosenIntegerRingUniformizer_pow_mul_mem_integerRingStatement` applied to all its parameters in source order.
The field universe is arbitrary; the theorem retains the field, valuative
relation, topology and nonarchimedean local-field instances, together with
every explicit element and proof hypothesis of its target.

Write `x` as a fraction `a / b` of integer-ring elements with nonzero
denominator. The DVR factorization theorem writes `b` as a unit times a
natural power of the chosen irreducible. Choosing that exponent cancels the
uniformizer power in the field; the remaining element is the integer
`a * u⁻¹`. The proof checks the nonzero factors and the compatibility of
unit inverses with the algebra map before using its integer-ring membership.

The original is Naganori Yamaguchi's
`LocalFieldTheory.exists_chosenIntegerRingUniformizer_pow_mul_mem_integerRing`, source unit M133.020,
lines 294–342 (target and proof) and 56–60 (local prerequisite) of
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
the exact named Prop target. The source proof is otherwise unchanged. Its M133.005 prerequisite is
reproved privately as `chosenIrreducible` by the defining choice specification,
since that theorem is not yet published. The named target is unfolded before
the source argument. There is no import or public duplicate of an unpublished
proof.
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
