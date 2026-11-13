# Recovering a closed subgroup from its abstract fixed field

`Langlands.NYLL.LocalClassFieldTheory.closedFixingSubgroup_abstractFixedField_eq`
proves exactly
`Langlands.NYLL.LocalClassFieldTheory.closedFixingSubgroup_abstractFixedField_eqStatement k Ω H`.
Here `k Ω : Type 0` are fields with an algebra and `[IsGalois k Ω]`, and
`H` is an arbitrary closed subgroup of `Gal(Ω/k)`. Taking the closed fixing
subgroup of `abstractFixedField k Ω H` recovers `H`.

The implemented proof is the source proof. Closed-subgroup extensionality reduces
the equality to membership in the underlying subgroups. The published
`abstractFixedField` is `IntermediateField.fixedField H.toSubgroup`, and the
underlying subgroup of `RamificationTheory.closedFixingSubgroup` is its ordinary
fixing subgroup. Mathlib's `InfiniteGalois.fixingSubgroup_fixedField H` rewrites
this subgroup to `H.toSubgroup`; reflexivity closes the membership equivalence.
The only NYLL inputs are the published target and its imports, including those
two definitions. No finiteness or openness assumption is needed.

Adapted by Worker 213 from Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`,
lines 38–46 (M099.002), with the source telescope at line 31. Registered source:
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
