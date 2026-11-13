# The bottom fixing subgroup is the abstract base field

`Langlands.NYLL.LocalClassFieldTheory.closedFixingSubgroup_bot_eq_baseField`
proves exactly
`Langlands.NYLL.LocalClassFieldTheory.closedFixingSubgroup_bot_eq_baseFieldStatement K Ω`
for fields `K Ω : Type 0`, an algebra `K → Ω` and `[IsGalois K Ω]`.
The bottom intermediate field has the whole ambient Galois group as its fixing
subgroup, so its closed fixing subgroup equals the distinguished abstract base.

The implemented proof is the source proof: apply closed-subgroup extensionality,
unfold membership in `closedFixingSubgroup` and `ClassFormation.baseField`, then
rewrite by Mathlib's `IntermediateField.fixingSubgroup_bot`. The only NYLL
inputs are the published target and its imports, including those two definitions.
There is no finite-extension or local-field assumption.

Adapted by Worker 213 from Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/GaloisExtensionQuotient.lean`,
lines 31–39 (M089.001). Registered source:
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The retained source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

Modification record: extract this theorem into the required focused module;
prefix its namespace with `Langlands.NYLL`; replace broad source imports by the
published target module; state the conclusion using the exact named Prop target;
retain the original binders and proof body; omit unused namespace openings.
The original copyright and author header is retained. Apache-2.0 license and
notices remain in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support proof does not discharge a host reciprocity or cohomology target.
