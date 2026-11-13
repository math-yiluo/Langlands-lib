# NYLL M010.004: the underlying subgroup of the base field

Worker 186 adapts Naganori Yamaguchi's source theorem
`ClassFormation.baseField_toSubgroup` as
`Langlands.NYLL.ClassFormation.baseField_toSubgroup`. Its declared type is
exactly `Langlands.NYLL.ClassFormation.baseField_toSubgroupStatement G`,
with explicit `G : Type u`, followed by `[Group G]` and
`[TopologicalSpace G]`. The conclusion unfolds to
`(baseField G).toSubgroup = ⊤`. It requires no topological-group,
compactness, finiteness or degree-map hypothesis.

The only direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Statements`.
That published module imports `Fields.Definitions`, whose `baseField` stores
`⊤` as its `toSubgroup` field and uses `isClosed_univ` for closedness.
Unfolding the target and projecting this definition reduces both sides of
the equality to the same subgroup. The implemented proof is `rfl`, exactly
as in the source. It invokes no supporting theorem or additional axiom.
The transitive imports are those already supplied by the published target;
no new supporting module is needed.

The source is unit M010.004 of
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`,
lines 54–58 (docstring 54, `@[simp]` 55, theorem 56–57 and `rfl` 58), in
`n-yamaguchi-0729/ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`. The retained original is at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`;
its SHA-256 is
`841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.
The registered source collection is
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the supplementary registration is
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The published target and its documentation were read at Library commit
`ed924aef420de137b4cbaa3b063a3618afcd73fd`.

The modifications are the focused module path, the `Langlands.NYLL`
namespace prefix, replacement of the source's full import list with the
published target import, and use of the named proposition as the theorem's
result type. The source's unused noncomputable section is omitted.
The source `@[simp]` attribute is deliberately omitted; the theorem remains
available for explicit use. Its name, universe, parameter order, hypotheses,
docstring and reflexivity proof are preserved.

The original copyright, author and Apache-2.0 header are retained. The
existing `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`)
are preserved unchanged. This support equality establishes no host
class-formation, cup, transfer, Tate or reciprocity result.
