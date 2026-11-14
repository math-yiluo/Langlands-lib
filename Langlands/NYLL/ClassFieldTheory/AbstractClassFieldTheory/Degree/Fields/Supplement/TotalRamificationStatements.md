# NYLL M010: total-ramification image criteria

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`,
SHA-256 `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.
The retained source is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
`nyll-classfieldtheory-fbd320cd-supplement` has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

The original prefix in the following table is
`ClassFormation.DegreeData.`; the adapted prefix is
`Langlands.NYLL.ClassFormation.DegreeData.`.

| Unit | Source declaration | Source lines | Adapted declaration |
| --- | --- | --- | --- |
| M010.064 | `GaloisSubextension.isTotallyRamified_iff_image_le` | 543–548, statement 543–547 | `GaloisSubextension.isTotallyRamified_iff_image_leStatement` |
| M010.076 | `FiniteAbstractExtension.isTotallyRamified_iff_image_le` | 635–639, statement 635–638 | `FiniteAbstractExtension.isTotallyRamified_iff_image_leStatement` |

Both declarations retain implicit `{G : Type u}`, instance `[Group G]`,
then instance `[TopologicalSpace G]`. M010.064 next has implicit
`{K : ClosedSubgroup G}`, explicit `(L : GaloisSubextension K)`, then
explicit `(D : DegreeData G)`. Its Prop body is exactly

```lean
L.IsTotallyRamified D ↔
  K.toSubgroup.map D.degree.toMonoidHom ≤
    L.field.toSubgroup.map D.degree.toMonoidHom
```

M010.076 next has explicit `(E : FiniteAbstractExtension G)`, inherited
from the source section variable, then explicit `(D : DegreeData G)`.
Its Prop body is exactly

```lean
E.IsTotallyRamified D ↔
  E.base.toSubgroup.map D.degree.toMonoidHom ≤
    E.field.toSubgroup.map D.degree.toMonoidHom
```

These are the original subgroup-image criteria, with the upper field
represented contravariantly. The finite extension retains its bundled
finite-quotient data; the Galois subextension retains its bundled normality.
No ambient profiniteness, finite-dimensionality, or extra hypotheses are added.

Worker 357 extracts these two source declarations, prefixes their namespace,
converts each theorem to a `def` returning `Prop` with the suffix `Statement`,
and omits both theorem proofs. The pure proposition definitions need no
`noncomputable section`. Comments and whitespace are adjusted. The whole-file
source imports are replaced by the published
`...Degree.Fields.GaloisSubextension.Definitions` and
`...Degree.Fields.FiniteExtension.Definitions` modules. All mathematical
objects are reused by Lean name; neither this file nor its targets declares
an instance. The source theorem on the underlying `AbstractExtension` is
already published, but these two exact named source targets are retained
for separate proof work.

In environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`, focused `lean_check`
builds and exact declaration inspections succeeded without warnings for
both targets; both inspections report `statement_returns_prop: true`.
These checks do not prove either target or establish independent acceptance.

The original copyright and author header is retained. Attribution remains in
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This is source support and supplies no host class-formation or reciprocity theorem.
