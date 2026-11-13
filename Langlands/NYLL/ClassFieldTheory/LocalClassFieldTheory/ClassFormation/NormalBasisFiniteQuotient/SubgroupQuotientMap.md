# NYLL map from a principal-unit quotient to a subgroup quotient

Worker 197 adapts M148.002 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisFiniteQuotient.lean`,
lines 60–68 (section variables at lines 26–31).
The readable original is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`,
registered as `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The supplemental registration is `nyll-classfieldtheory-fbd320cd-supplement`,
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
There is no applicable NYLL entry in the Library's `notes/errata/`.

| Original declaration | Adapted declaration |
| --- | --- |
| `LocalClassFieldTheory.integerUnitsModPrincipalUnitsToSubgroupQuotient` | `Langlands.NYLL.LocalClassFieldTheory.integerUnitsModPrincipalUnitsToSubgroupQuotient` |

Given an integer-unit subgroup `V` containing the principal-unit subgroup of
level `m`, this is the actual group homomorphism from the named level quotient
to the quotient by `V`. It descends the canonical quotient homomorphism by
`integerUnitsModPrincipalUnitsAtLevelLift`. Its retained proof term verifies
that each principal unit at level `m` maps to the identity using the supplied
containment `h`. The data body, including this proof term, is unchanged.
Surjectivity is a separate statement.

The effective source telescope is the single universe `u`, explicit
`(L : Type u)`, instances `[Field L] [ValuativeRel L]`, then explicit
`(m : Nat) (V : Subgroup 𝒪[L]ˣ) (h : principalUnits L m ≤ V)`.
The source's parameters involving the unused field `K`, and its topology,
local-field, extension and module-finiteness instances, do not occur in this
definition's type or body and Lean omits them in the original. The focused
section displays exactly the effective source parameters with their binder
kinds and order.

The published module
`Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.PrincipalUnits.QuotientReps.Definitions`
supplies `Langlands.NYLL.CyclicCohomology.IntegerUnitsModPrincipalUnitsAtLevel`
and `Langlands.NYLL.CyclicCohomology.integerUnitsModPrincipalUnitsAtLevelLift`.
These are the namespaced adaptations of the source quotient and quotient lift;
their original definitions are in `PrincipalUnits/QuotientReps.lean`, lines
31–33 and 88–93. The principal-unit subgroup is the published
`Langlands.NYLL.LocalFieldTheory.principalUnits`. No substitute quotient,
additional assumption or new instance is introduced.

Modifications are the namespace prefix, extraction into this focused pair,
the focused import replacing the original broad imports, and omission of
unrelated source commands and unused namespace openings. The original
copyright and author header is retained. The Apache-2.0
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain applicable. This
supporting map proves no class-formation or reciprocity theorem.
