# The multiplicative value of an integer-ring irreducible (M133.014)

`Langlands.NYLL.LocalFieldTheory.valueGroupWithZeroIsoInt_of_integerRing_irreducible` proves the exact published target
`Langlands.NYLL.LocalFieldTheory.valueGroupWithZeroIsoInt_of_integerRing_irreducibleStatement` applied to all its parameters in source order.
The field universe is arbitrary; the theorem retains the field, valuative
relation, topology and nonarchimedean local-field instances, together with
every explicit element and proof hypothesis of its target.

The proof imports only `IdealQuotients.Statements` and follows the
source DVR argument. Its three private source helpers first show that every
`WithZero (Multiplicative Int)` value below one is at most `ofAdd (-1)`,
then characterize the greatest value below one, and transport this property
through Mathlib's order and monoid isomorphism
`IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt`.

Mathlib's `Valuation.integer.v_irreducible_lt_one` puts the value of `ϖ`
below one. To prove maximality, valuation surjectivity realizes any value
`δ < 1` by a field element. The zero case is immediate. Otherwise the element
lies in the integer ring and is a nonunit, hence in its maximal ideal. The
DVR equality `hϖ.maximalIdeal_eq` puts it in the span of `ϖ`.
`Valuation.integer.coe_span_singleton_eq_setOfPred_le_v_coe` converts that
membership into the required valuation inequality. The transported maximality
then gives exactly `ofAdd (-1)`. The only public theorem in this module is
the required M133.014 proof.

The original is Naganori Yamaguchi's
`LocalFieldTheory.valueGroupWithZeroIsoInt_of_integerRing_irreducible`, source unit M133.014,
lines 166–208, with private helpers at lines 110–158 of
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
the exact named Prop target. The three source-private helpers (M133.011–.013) are retained privately
with their original proof routes. References to Mathlib's value-group
isomorphism are rooted to avoid the NYLL namespace with the same class name.
An initial `change` unfolds the exact target. All other proof steps, including
the zero branch, integer arithmetic and principal-ideal comparison, are
unchanged. The source helper names remain private to this module; no
unpublished NYLL proof is imported.
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
