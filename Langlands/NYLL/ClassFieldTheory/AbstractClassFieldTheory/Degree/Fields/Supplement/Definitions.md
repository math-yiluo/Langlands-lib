# NYLL M010: finite residue quotient from a relative inclusion

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

M010.110, source lines 957–984, is
`ClassFormation.DegreeData.FiniteResidueAbstractField.ofRelativeInclusion`.
It is adapted as
`Langlands.NYLL.ClassFormation.DegreeData.FiniteResidueAbstractField.ofRelativeInclusion`.
The constructor is data valued and keeps the source body, including its
finiteness proof.

The complete telescope, in order, is implicit `{G : Type u}`, instance
`[Group G]`, instance `[TopologicalSpace G]`, explicit `(D : DegreeData G)`,
explicit `(field : ClosedSubgroup G)`, explicit
`(base : FiniteResidueAbstractField D)`, explicit
`(below : field.toSubgroup ≤ base.field.toSubgroup)`, then the named instance

```lean
[finiteRelativeResidueQuotient : Finite
  (↥(base.field.toSubgroup.map D.degree.toMonoidHom) ⧸
    (field.toSubgroup.map D.degree.toMonoidHom).subgroupOf
      (base.field.toSubgroup.map D.degree.toMonoidHom))]
```

The return type is `FiniteResidueAbstractField D`. The preceding source
namespace variable `{D : DegreeData G}` is shadowed by the explicit `D` and
adds no second parameter. Neither the ambient group nor its topology has
an extra assumption.

The `field` projection is the supplied closed subgroup. For
`finiteResidueQuotient`, the implementation rewrites its cardinality as
`D.residueDegreeCardinal field`, constructs the actual `AbstractExtension`
with endpoints `field` and `base.field` and containment `below`, then uses
the cardinal tower identity to write the absolute residue cardinal as the
product of the relative and base residue cardinals. Each factor is below
`aleph0` by the supplied relative finiteness and the base's bundled absolute
finiteness. `Cardinal.mul_lt_aleph0_iff` and
`Cardinal.lt_aleph0_iff_finite` finish the unchanged source proof.

Worker 357 extracts this source unit and prefixes its namespace with
`Langlands.NYLL`. The nested namespace commands are combined and the docstring
is lightly edited. The source's broad imports are replaced by the published
`...Degree.Fields.FiniteResidue.Definitions`,
`...Degree.Fields.U019.Proofs`, and
`...Degree.Fields.AbstractExtension.U036.Proofs` modules. These supply the
source data and the two actual cardinality identities by Lean name.
The declaration from `noncomputable def` through the end of its body is
textually unchanged from source lines 957–984. No proof is replaced by a
hypothesis, no alternate quotient is substituted, and no instance is declared.

Focused compilation and declaration inspection in environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` succeeded without warnings.
The inspection identifies a definition with universe parameter `u` and
only the standard `propext`, `Classical.choice`, and `Quot.sound` assumptions.
This check establishes compilation, not independent acceptance.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This constructor supplies no host class-formation or reciprocity theorem.
