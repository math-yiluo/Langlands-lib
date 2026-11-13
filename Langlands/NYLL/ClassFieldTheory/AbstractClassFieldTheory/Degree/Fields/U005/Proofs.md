# NYLL M010.005: inclusion in the distinguished base field

`Langlands.NYLL.ClassFormation.le_baseField` proves the published proposition
`Langlands.NYLL.ClassFormation.le_baseFieldStatement K`. Its parameters are
implicit `G : Type u`, instances `[Group G]` and `[TopologicalSpace G]`, and
explicit `K : ClosedSubgroup G`, in that order. The conclusion unfolds to
`K.toSubgroup ≤ (baseField G).toSubgroup`.

The implemented proof is the source term `le_top`. The published definition
of `baseField G` has `toSubgroup := ⊤`, so unfolding the statement and this
projection reduces the goal to `K.toSubgroup ≤ ⊤`. Mathlib's order theorem
`le_top` supplies precisely that inclusion. The only direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Statements`,
which provides the proposition and its existing data dependencies. The proof
uses no degree datum, inertia result, residue result, or additional hypothesis.
In particular it does not depend on a proof of `baseField_toSubgroupStatement`.

The source is Naganori Yamaguchi's
`n-yamaguchi-0729/ClassFieldTheory`, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`,
unit M010.005: docstring line 60, theorem signature lines 61–62 and proof
line 63. The source file SHA-256 is
`841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`.
The retained source is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Its registration is `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

Worker 187 extracts only this theorem, prefixes the source namespace with
`Langlands.NYLL`, replaces the source imports with the published target
module, and expresses the conclusion through that target. The original
docstring, universe, parameter order and proof term are retained. This is
the abstract subgroup inclusion of the source; it discharges no host
class-formation, cup, transfer, Tate or reciprocity target.

The original copyright and author header is retained under Apache-2.0.
The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are preserved;
their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1` and
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
