# NYLL surjectivity statement for the subgroup quotient map

Worker 197 adapts M148.003 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/ClassFormation/NormalBasisFiniteQuotient.lean`,
lines 72–80 (target at lines 72–75, `omit` command at line 70 and section
variables at lines 26–31).
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
| `LocalClassFieldTheory.integerUnitsModPrincipalUnitsToSubgroupQuotient_surjective` | `Langlands.NYLL.LocalClassFieldTheory.integerUnitsModPrincipalUnitsToSubgroupQuotient_surjectiveStatement` |

The proposition says that the actual homomorphism from the named level-`m`
integer-unit quotient to the quotient by `V` is surjective when `V` contains the
level-`m` principal-unit subgroup. The body is exactly the source target,
`Function.Surjective (integerUnitsModPrincipalUnitsToSubgroupQuotient L m V h)`.
The imported `SubgroupQuotientMap` pair supplies the source construction under
`Langlands.NYLL.LocalClassFieldTheory.integerUnitsModPrincipalUnitsToSubgroupQuotient`.
It must be integrated before or alongside this statement.

The source's single universe `u` and full effective theorem telescope are
retained in order and with the same binder kinds: explicit `(L : Type u)`,
instances `[Field L] [ValuativeRel L]`, then explicit `(m : Nat)`,
`(V : Subgroup 𝒪[L]ˣ)` and `(h : principalUnits L m ≤ V)`.
The original explicitly omits `[TopologicalSpace L]` and
`[IsNonarchimedeanLocalField L]` for this theorem. Its section variables involving
the unused carrier `K`, including the extension and module-finiteness instances,
are not included in the original theorem's effective telescope. The proposition
definition binds the retained parameters explicitly.

Modifications are the `Langlands.NYLL` namespace prefix, the `Statement` suffix,
replacement of the theorem and proof by a `Prop`-valued definition of its exact
target, and extraction into this focused pair. The focused import replaces the
source's broad imports; unrelated commands and unused namespace openings are
omitted. No proof of the target, extra assumption or new instance is introduced.

The original copyright and author header is retained. The Apache-2.0
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain applicable. This
supporting statement proves no class-formation or reciprocity theorem.
