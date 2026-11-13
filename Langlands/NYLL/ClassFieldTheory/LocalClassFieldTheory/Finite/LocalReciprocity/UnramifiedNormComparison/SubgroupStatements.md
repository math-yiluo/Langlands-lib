# Actual unramified norm subgroups: proposition targets

These two closed propositions concern a finite unramified Galois extension
of nonarchimedean local fields `K L : Type`. They reuse the actual published
`Langlands.NYLL.LocalFieldTheory.localNormSubgroup K L`, the image of the
norm on field units, and the published
`Langlands.NYLL.LocalClassFieldTheory.unramifiedNormSubgroup K (Module.finrank K L)`,
whose membership means divisibility of the normalized valuation by the degree.

| Source unit | Target after `Langlands.NYLL.LocalClassFieldTheory.` | Conclusion |
| --- | --- | --- |
| M267.001 | `localNormSubgroup_le_unramifiedNormSubgroupStatement` | The actual norm subgroup is contained in the valuation-divisibility subgroup. |
| M267.010 | `normSubgroup_eq_unramifiedNormSubgroup_of_isIntegralClosureStatement` | The actual norm subgroup equals the valuation-divisibility subgroup. |

Each declaration preserves the complete source section telescope: `K L : Type`
at universe zero, field, valuation-relation, topology and nonarchimedean local
field instances on both; `Algebra K L`, `FiniteDimensional K L`, `IsGalois K L`;
a valuation-extension instance; `IsIntegralClosure 𝒪[L] 𝒪[K] L`;
`Module.Finite 𝒪[K] 𝒪[L]`; and the published
`Langlands.NYLL.LocalFieldTheory.IsNonarchimedeanLocalField.IsUnramifiedValuedExtension K L`.
The hypotheses are quantified instances in the original order. No replacement
unramifiedness predicate or chosen norm map is supplied. The degree is the
actual module finrank. These are proposition definitions; no proof is asserted.

## Source and changes

The original module is
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/UnramifiedNormComparison.lean`
in Naganori Yamaguchi's ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
The full source was read; its SHA-256 is
`a955313b05e5cdeb8bd4e9c6c76e466c956fe7231bb6fd90f4945a57e564ad26`.
It is registered in `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`, under
`n-yamaguchi-0729--ClassFieldTheory/source/` followed by that path.
No applicable errata entry was found in the project notes.

The shared original section parameters are at source lines 34–44.
M267.001 is `LocalClassFieldTheory.localNormSubgroup_le_unramifiedNormSubgroup`,
lines 47–59. M267.010 is
`LocalClassFieldTheory.normSubgroup_eq_unramifiedNormSubgroup_of_isIntegralClosure`,
lines 157–167. Each original name is preserved with the `Langlands.NYLL` prefix
and a `Statement` suffix. Worker 205 added a modification notice, extracted the
statements from their theorems, and universally closed the original telescope
as `def ... : Prop`. The conclusions and hypotheses are unchanged. The source
proofs remain separate obligations.

The imports reuse published `NormQuotient.U001.Definitions`,
`UnramifiedNormSubgroup.U011.Definitions` and
`FiniteUnramified.Definitions`, together with `Mathlib.FieldTheory.Galois.Basic`.
They suffice to state the targets without importing the local reciprocity
isomorphism or the later quotient comparison constructions.
No local or global instance is introduced.

The original copyright and author header is retained, with Apache-2.0 license
and notices in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
No earlier adaptation or another worker's draft was reused.

## Development checks

Focused `lean_check` calls compiled the module without errors or warnings and
inspected each named declaration as a proposition definition with
`statement_returns_prop: true` and no universe parameters, preserving the
source universe-zero telescope. The entry module uses only the three published
data imports and Mathlib listed above. Independent semantic acceptance and the
exact proofs are separate obligations.
