# The additive value of an irreducible field unit (M133.015)

`Langlands.NYLL.LocalFieldTheory.v_integerRingIrreducibleFieldUnit` proves the exact published target
`Langlands.NYLL.LocalFieldTheory.v_integerRingIrreducibleFieldUnitStatement` applied to all its parameters in source order.
The field universe is arbitrary; the theorem retains the field, valuative
relation, topology and nonarchimedean local-field instances, together with
every explicit element and proof hypothesis of its target.

The module imports only `IdealQuotients.Statements`. The proof unfolds
the published NYLL definition of `IsNonarchimedeanLocalField.v`. Under the
hypothesis `hu`, the value of the unit equals the value of the integer-ring
irreducible. A private lemma `irreducibleValue` proves the M133.014
normalization locally: the irreducible value is the greatest value below one,
because the maximal ideal is its singleton span. Three private ordered-group
helpers transport this greatest-value characterization through Mathlib's
value-group isomorphism and identify the result as `ofAdd (-1)`.

The main proof uses nonvanishing of the value, applies `WithZero.coe_injective`
and `WithZero.coe_unzero`, and substitutes this multiplicative normalization.
Taking `Multiplicative.toAdd` then gives the integer `-1` definitionally.
The local normalization uses valuation surjectivity, the canonical DVR
instance, `Valuation.integer.v_irreducible_lt_one`,
`Irreducible.maximalIdeal_eq`, and the valuation description of a singleton
span, all available from Mathlib through the target imports.

The original is Naganori Yamaguchi's
`LocalFieldTheory.v_integerRingIrreducibleFieldUnit`, source unit M133.015,
lines 212–233; private normalization follows lines 110–208 of
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
the exact named Prop target. The original M133.015 proof route is retained. Its M133.014
prerequisite and the source-private helpers at lines 110–158 are reproved
locally and privately; the adapted public M133.014 name is not duplicated
or imported before publication. The helper's written type is the existing
M133.014 Prop target, explicitly unfolded when applying it. An initial `change` unfolds the M133.015 target, and
Mathlib's value-group isomorphism is rooted to avoid a namespace collision.
The NYLL normalized valuation is resolved in the adapted namespace.
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
