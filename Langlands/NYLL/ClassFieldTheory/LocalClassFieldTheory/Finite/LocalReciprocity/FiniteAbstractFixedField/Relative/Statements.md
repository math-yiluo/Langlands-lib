# Relative fixing subgroup image and normality targets

Adapted by Worker 203 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/FiniteAbstractFixedField.lean`.
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M099.010 | `map_extensionSubgroup_abstractSubgroupEquiv` (124–165) | `map_extensionSubgroup_abstractSubgroupEquivStatement` |
| M099.011 | `abstractRelativeFixingSubgroup_normal` (167–180) | `abstractRelativeFixingSubgroup_normalStatement` |

Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory` unless fully qualified.

Prefix the namespace and convert both source theorems to Prop-valued definitions with `Statement` suffix. Preserve the complete source telescope and binder order. In particular both targets explicitly retain `[IsGalois k Ω]`: the normality theorem uses it in its source proof through the subgroup/Galois equivalence even though its conclusion alone would not force Lean to retain it. Source proofs are omitted. Imports are reduced to the relative and initial fixed-field data.

As directed by the task context, replace `CyclicCohomology.extensionSubgroup K L hLK` by its exact Mathlib body `L.toSubgroup.subgroupOf K.toSubgroup` (M004.002, original `Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`, lines 47–54). The mapped subgroup and actual fixing subgroup are unchanged. The first target identifies these actual subgroups under `abstractSubgroupEquivGaloisGroup`; the second transfers a given relative normality witness to the concrete fixing subgroup. These are statements for separate proof tasks, not normality instances or assumed results.

The original copyright and author header is retained. Apache-2.0 attribution
and notices are in `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`.
This support unit makes no claim to discharge the host class-formation, cup,
transfer, Tate or reciprocity targets.

The expected unused-variable warning for the explicit `hnormal` binder is retained to preserve the source telescope.
