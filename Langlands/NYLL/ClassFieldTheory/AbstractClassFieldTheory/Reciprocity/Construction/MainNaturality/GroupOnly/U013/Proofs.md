# NYLL M066.013: finiteness of the composite quotient in the naturality tower

`Langlands.NYLL.PortInternal.M066.d013` proves the published proposition
`Langlands.NYLL.PortInternal.M066.d013Statement` of module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality.GroupOnly.Statements`.
It is the port of the source-private theorem
`ClassFormation.finiteReciprocityNaturality_tower_finite`.

## Statement

The parameters are, in order, the section variables implicit `G : Type u` with
instances `[Group G]` and `[TopologicalSpace G]`, explicit
`K K' L' : ClosedSubgroup G`, `hK'K : K'.toSubgroup ≤ K.toSubgroup` and
`hL'K' : L'.toSubgroup ≤ K'.toSubgroup`, and the instances
`[Finite (K.toSubgroup ⧸ K'.toSubgroup.subgroupOf K.toSubgroup)]` and
`[Finite (K'.toSubgroup ⧸ L'.toSubgroup.subgroupOf K'.toSubgroup)]`. The binders
are written exactly as in the published statement. The type of the theorem is
exactly `Langlands.NYLL.PortInternal.M066.d013Statement K K' L' hK'K hL'K'`,
which unfolds to

```lean
Finite (K.toSubgroup ⧸ L'.toSubgroup.subgroupOf K.toSubgroup)
```

In words: in a tower `G_{L'} ≤ G_{K'} ≤ G_K` of closed subgroups in which
`G_{K'}` has finite index in `G_K` and `G_{L'}` has finite index in `G_{K'}`, the
subgroup `G_{L'}` has finite index in `G_K`: the quotient of `K.toSubgroup` by
`L'.toSubgroup.subgroupOf K.toSubgroup` is finite.

## Implemented proof

The module contains the single theorem
`Langlands.NYLL.PortInternal.M066.d013`, declared with `_root_` inside
`namespace Langlands.NYLL.ClassFormation` as in the statement module. Its proof
is the term `relativeTowerQuotientFinite K K' L' hL'K' hK'K`, the published
M026.014 (module `...Degree.NormLaws.U014.Proofs`) applied with `K` as the
base, `K'` as the middle and `L'` as the top. Its two finiteness instance
arguments are written there through the published `abbrev`
`extensionSubgroup`, whose bodies are the two `subgroupOf` quotients of the
binders above, so instance search finds the theorem's own hypotheses. Its type
`relativeTowerQuotientFiniteStatement K K' L' hL'K' hK'K` unfolds to
`Finite (K.toSubgroup ⧸ extensionSubgroup K L' (hL'K'.trans hK'K))`, which is
definitionally the unfolded target, so the term is accepted at the target type
without a `show`.

Imports: the required statement module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.MainNaturality.GroupOnly.Statements`
and the published proof module of `relativeTowerQuotientFinite`,
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.NormLaws.U014.Proofs`
(M026.014). No other declaration is used. The kernel axioms reported by
inspection are `propext`, `Classical.choice` and `Quot.sound`.

## Source correspondence and modifications

The source is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`, pinned
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Construction/MainNaturality.lean`,
SHA-256 `0107befcff3ba066d7663120d9aa823ae72911cef7d3e72c5eeb5cb95f73a533`,
retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Its registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`,
content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

| Unit | Source name | Source lines | Port |
| --- | --- | --- | --- |
| M066.013 | `ClassFormation.finiteReciprocityNaturality_tower_finite` (private) | docstring 403–404, statement 405–412, proof 413 | `Langlands.NYLL.PortInternal.M066.d013` |

The enclosing source context is `universe u` (line 19),
`namespace ClassFormation` (21), `noncomputable section` (32),
`section GroupOnly` (36) and `variable {G : Type u} [Group G] [TopologicalSpace G]`
(38); the source also opens `KummerTheory`, `CyclicCohomology`,
`CategoryTheory` (23, 25, 27) and `scoped BigOperators` (34), which the port
does not need. The port keeps the namespace under the prefix `Langlands.NYLL`,
the universe and the section variable.

Modifications, all by Worker 735:

- The namespace is prefixed with `Langlands.NYLL`; the source import is
  replaced by the two published modules listed above.
- The source-private theorem is published under the port-internal name
  `Langlands.NYLL.PortInternal.M066.d013`, without the `private` modifier, and
  its type is written as the published `d013Statement`. Following that
  statement, the source's `extensionSubgroup` quotients in the binders and the
  conclusion are written through their `Subgroup.subgroupOf` bodies.
- The source proof term `relativeTowerQuotientFinite K K' L' hL'K' hK'K` is
  retained unchanged.

This is a finiteness fact about the NYLL abstract-field model. It discharges no
host class-formation, cup, transfer, Tate or reciprocity target.

## Attribution

The original copyright, author and Apache-2.0 header is retained verbatim, and
the Lean module docstring records the modifications. The existing Library files
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are preserved unchanged; their
SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
