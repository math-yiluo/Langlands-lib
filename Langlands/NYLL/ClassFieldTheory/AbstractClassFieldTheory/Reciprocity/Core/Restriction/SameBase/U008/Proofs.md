# NYLL M075.008: equality of the two same-base restriction maps

Worker 190, 13 November 2026.

## Statement and scope

This pair proves the published target
`Langlands.NYLL.ClassFormation.finiteReciprocityNaturalityRestriction_sameBase_eq_restrictionStatement`
using the required theorem name
`Langlands.NYLL.ClassFormation.finiteReciprocityNaturalityRestriction_sameBase_eq_restriction`.
Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core.Restriction.SameBase.Statements`.
The statement and its imported definitions remain unchanged.

Let `G` be a group with a topology and let `L ≤ M ≤ K` be closed subgroups.
Assume that the subgroups of `K` obtained from `L` and `M` are normal.
The theorem identifies these actual homomorphisms from `K/L` to `K/M`:

```lean
finiteReciprocityNaturalityRestriction K K M L hMK (hLM.trans hMK) le_rfl hLM
abstractReciprocityRestriction K M L hLM hMK
```

The former comes from the subgroup inclusion `K → K` and the latter from
the identity homomorphism on `K`. The theorem is equality of these constructed
maps. It retains the source's arbitrary universe for `G`, group and topology
instances, explicit `K M L hLM hMK`, and named instance binders `hLnormal`
and `hMnormal`. It adds no finiteness or topological-group hypothesis.

## Implemented proof

The implementation follows the original proof:

```lean
  apply MonoidHom.ext
  intro q
  refine QuotientGroup.induction_on q ?_
  intro k
  rfl
```

`MonoidHom.ext` reduces equality of homomorphisms to equality of their
values. Quotient induction chooses a representative `k : K.toSubgroup`
for the source quotient. Both maps then compute to the class of the same
element in `K/M`, so reflexivity closes the goal. The argument uses the actual
quotient maps; no equality of restrictions is assumed.

The imported statement supplies both definitions:

- `finiteReciprocityNaturalityRestriction`, defined in the published
  `Construction.MainNaturality.Restriction.Definitions` module, uses
  `QuotientGroup.map` with `Subgroup.inclusion`.
- `abstractReciprocityRestriction`, defined in the published
  `Core.Restriction.Definitions` module, uses `QuotientGroup.map` with
  `MonoidHom.id`.

The proof uses Mathlib's `MonoidHom.ext` and
`QuotientGroup.induction_on`, followed by definitional reduction. It needs no
other NYLL proof theorem, including the separate restriction-on-representatives
or surjectivity targets.

## Original source and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean`,
lines 509–523. The declaration begins at line 509, its type occupies
lines 510–518, and the implemented proof is at lines 519–523.
The original map definition is at lines 457–472.
The source file SHA-256 is
`0fc1bd5c66d628b74e079fd54af4a9df7334343e38186983257da5ce6a8f06fb`.

The retained snapshot is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Registered sources are `external-lean-reuse-snapshots-2026-10-21`
(fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`)
and `nyll-classfieldtheory-fbd320cd-supplement`
(fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

| Source declaration | Published proof declaration |
| --- | --- |
| `ClassFormation.finiteReciprocityNaturalityRestriction_sameBase_eq_restriction` | `Langlands.NYLL.ClassFormation.finiteReciprocityNaturalityRestriction_sameBase_eq_restriction` |

Modifications are limited to the `Langlands.NYLL` namespace prefix, the
focused published-statement import, expressing the theorem's result as that
existing proposition applied to its parameters, and expanding
`CyclicCohomology.extensionSubgroup K L h` to
`L.toSubgroup.subgroupOf K.toSubgroup` in the normality binders.
The source abbreviation is defined by that exact Mathlib expression at
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean:51–54`.
The explicit theorem telescope preserves all source binders.
The proof itself is unchanged. The unused-variable linter is disabled locally
to retain the source instance names.

The original copyright, Apache-2.0 license statement and author header are
preserved in the Lean file. The inherited `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE` remain unchanged, with respective SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This support lemma proves M075.008 only. It establishes no host class-formation,
cup-product, transfer, Tate-cohomology or local-reciprocity target.

## Development validation

Lean service check `6f69301b-ba8b-41ab-b5c7-90958b0efd3f` compiled the proof
in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, with no errors or
warnings. Declaration inspection reported the original single universe
parameter and only `propext`, `Classical.choice` and `Quot.sound` as assumptions.
The theorem result is the published target applied to its parameters.
Independent review, exact-target validation and publication remain separate.
