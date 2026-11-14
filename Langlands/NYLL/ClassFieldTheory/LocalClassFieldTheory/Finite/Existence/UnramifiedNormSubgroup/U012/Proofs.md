# Membership in the unramified norm subgroup

The theorem
`Langlands.NYLL.LocalClassFieldTheory.mem_unramifiedNormSubgroup_iff`
has exactly the type of the published proposition
`Langlands.NYLL.LocalClassFieldTheory.mem_unramifiedNormSubgroup_iffStatement`.
For arbitrary `K : Type u`, instances `[Field K] [ValuativeRel K]
[TopologicalSpace K] [IsNonarchimedeanLocalField K]`, `n : Nat` and
`x : Kˣ`, it states

```text
x ∈ unramifiedNormSubgroup K n ↔
  (n : Int) ∣
    LocalFieldTheory.IsNonarchimedeanLocalField.valuationMap K (Additive.ofMul x).
```

Here the subgroup and valuation names are in their published
`Langlands.NYLL` namespaces. The arbitrary universe, parameter order and
local-field hypotheses are retained. There is no nonzero or positivity
assumption on `n`, so the theorem also covers `n = 0`.

The implemented proof introduces the universally quantified parameters of
the closed statement and applies `Iff.rfl`. Membership in the published
`unramifiedNormSubgroup K n` reduces definitionally to its carrier predicate,
which is precisely the displayed divisibility proposition. Both directions
are therefore the identity implication. This proof characterizes the
published valuation-divisibility subgroup; identification with a field
extension's norm subgroup is a separate result.

The sole import is the published
`UnramifiedNormSubgroup.SubgroupStatements` module. The target, subgroup and
valuation map are reused by Lean name. This contribution adds only the
theorem, with no new definitions or instances and no changes to the target
or its imported data.

## Source correspondence

This is M266.012, source theorem
`LocalClassFieldTheory.mem_unramifiedNormSubgroup_iff`, lines 143–147 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`
in Naganori Yamaguchi's ClassFieldTheory at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The complete original file was
read and its SHA-256 verified as
`ed3c13cfacb92012fb235f48817d5f23a043588ef78d7b2ed2e7ef4afa533b12`.
It is registered under `external-lean-reuse-snapshots-2026-10-21`,
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`,
at `n-yamaguchi-0729--ClassFieldTheory/source/` followed by the path above.
No applicable entry was found in the project errata notes.

Worker 532 extracted this theorem, added the namespace prefix and
modification record, replaced the original theorem telescope by the exact
closed Library statement, and replaced the original imports with the focused
published target. After introducing that statement's parameters, the proof
is the original `Iff.rfl`. The original copyright and author header is
retained verbatim. Apache-2.0 license and notices are published in
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. No other worker's draft
or compatibility patch was reused.
