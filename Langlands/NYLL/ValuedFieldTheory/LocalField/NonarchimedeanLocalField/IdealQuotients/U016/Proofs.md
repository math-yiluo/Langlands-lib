# The inverse of an irreducible integer-ring field unit has normalized value one (M133.016)

`Langlands.NYLL.LocalFieldTheory.v_integerRingIrreducibleFieldUnit_inv` proves the exact published target
`Langlands.NYLL.LocalFieldTheory.v_integerRingIrreducibleFieldUnit_invStatement` applied to all its parameters in source order.
The field universe is arbitrary; the theorem retains the field, valuative
relation, topology and nonarchimedean local-field instances, together with
every explicit element and proof hypothesis of its target.

The proof first privately establishes that an irreducible integer-ring element
has multiplicative normalized value `ofAdd (-1)`. It uses the DVR maximal-ideal
generator property and valuation surjectivity to show that this is the greatest
value below one, then uses the order isomorphism to multiplicative integers.
Valuations and the value-group isomorphism preserve inversion, so the inverse
field unit has value `ofAdd 1`. Injectivity of the nonzero coercion removes
`WithZero.unzero`, and taking the additive exponent gives exactly `1`.

The original is Naganori Yamaguchi's
`LocalFieldTheory.v_integerRingIrreducibleFieldUnit_inv`, source unit M133.016,
lines 237–244 (target) and 110–208 (local prerequisites) of
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
the exact named Prop target. The sibling M128.006 inverse theorem and M133.015 were not published in the
Library when this candidate was prepared. Instead of importing them, this proof
computes the inverse value directly using Mathlib `map_inv₀`. The local
`irreducibleValue` prerequisite and its three private helpers are the source
M133.010–.014 route, retained privately under non-conflicting names. Thus this
module imports only the exact statement module; it introduces no public copy
of another target.
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
