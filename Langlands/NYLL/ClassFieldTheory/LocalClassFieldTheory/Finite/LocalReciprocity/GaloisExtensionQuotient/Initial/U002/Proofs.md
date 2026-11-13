# Fixing subgroups lie in the base fixing subgroup

`Langlands.NYLL.LocalClassFieldTheory.fixingSubgroupLeBase` proves exactly
`Langlands.NYLL.LocalClassFieldTheory.fixingSubgroupLeBaseStatement K Ω E`
for fields `K Ω : Type 0`, an algebra `K → Ω`, `[IsGalois K Ω]` and an
intermediate field `E`. The subgroup fixing `E` lies in the subgroup fixing
the bottom intermediate field.

The implemented proof is the source's single application of Mathlib's
`IntermediateField.fixingSubgroup_le` to `bot_le`. Membership in the published
`RamificationTheory.closedFixingSubgroup` reduces to the ordinary fixing subgroup,
so the Mathlib result has the exact target after definitional reduction. It
uses the published target module and its imports, and does not require the
separate bottom-subgroup equality theorem.

Adapted by Worker 213 from Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean`,
lines 41–47 (M089.002). Registered source:
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The retained source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

Modification record: extract this theorem into the required focused module;
prefix its namespace with `Langlands.NYLL`; replace broad source imports by the
published target module; express the conclusion with the exact named Prop target;
retain the source binders and proof term; omit unused namespace openings.
The original copyright and author header is retained. Apache-2.0 license and
notices remain in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support proof does not discharge a host reciprocity or cohomology target.
