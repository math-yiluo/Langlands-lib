# Cardinality of an unramified valuation quotient: proposition target

`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormQuotient_card_eq_degreeStatement`
is the closed proposition that, for a nonarchimedean local field `K : Type u`
and a natural degree `n` with `[NeZero n]`,
`Nat.card (Kˣ ⧸ unramifiedNormSubgroup K n) = n`.
The subgroup is the published valuation-divisibility subgroup of the full field
unit group. This target does not itself identify it with an extension norm
subgroup, and no proof is asserted here.

The original arbitrary universe `u`, field, valuation relation, topology and
local-field hypotheses are retained, followed by `n` and its `NeZero` instance.
The nonzero hypothesis is essential to this exact source statement. The target
uses `Nat.card`, which is defined for every type; it requires no additional
chosen `Fintype` structure or finiteness hypothesis.

## Source and changes

This adapts M266.024, theorem
`LocalClassFieldTheory.unramifiedNormQuotient_card_eq_degree`, lines 244–253 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`
in Naganori Yamaguchi's ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
The full source was read; its SHA-256 is
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
It is registered in `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/` followed by the path above.
No applicable errata entry was found in the project notes.

The adapted declaration is
`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormQuotient_card_eq_degreeStatement`.
Worker 205 added the namespace prefix, modification notice and Statement suffix,
and universally quantified the unchanged source telescope in a `def ... : Prop`.
The source proof is reserved for a focused proof successor. That proof uses the
valuation quotient equivalence M266.020, but the target itself needs only the
published subgroup and Mathlib's quotient and cardinality definitions.

The imports are published `UnramifiedNormSubgroup.U011.Definitions`,
`Mathlib.GroupTheory.QuotientGroup.Defs` and
`Mathlib.SetTheory.Cardinal.Finite`. No instance is introduced.
The original copyright and author header is retained, with Apache-2.0 license
and notices in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
No earlier adaptation or another worker's draft was reused.

A focused Lean-service check in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` compiled the target with zero errors
and warnings. Inspection reported `statement_returns_prop: true` and universe
parameter `u`, confirming that these reduced imports suffice to state the
source cardinality target before the equivalence and proof are published.
