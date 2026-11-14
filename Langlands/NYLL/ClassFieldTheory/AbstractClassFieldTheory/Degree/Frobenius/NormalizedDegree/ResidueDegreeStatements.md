# NYLL M011: relative and absolute residue degrees

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Frobenius.lean`,
SHA-256 `d99a9993cdb5685118cd9b88a45c0a4e46aee57346e72566be042091bb5daa07`.
The retained source is under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
`nyll-classfieldtheory-fbd320cd-supplement` has fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

M011.017 is the theorem
`ClassFormation.DegreeData.FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegree`,
source lines 233–246, with statement at lines 233–236. Its adapted name is
`Langlands.NYLL.ClassFormation.DegreeData.FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegreeStatement`.

The complete telescope is implicit `{G : Type*}` (one unconstrained universe),
instance `[Group G]`, instance `[TopologicalSpace G]`, explicit
`(D : DegreeData G)`, then explicit `(E : FiniteResidueAbstractExtension D)`.
The exact Prop body is

```lean
(E.residueDegree : ℕ) * (E.base.residueDegree : ℕ) =
  (E.field.residueDegree : ℕ)
```

The leftmost factor is the positive relative residue degree of the actual
finite-residue extension. The second and right-hand factors are the base's
and field's positive absolute residue degrees, all coerced to `ℕ` as in the
source. Finiteness of the extension quotient and both endpoint residue
quotients remains bundled in `E`. The statement adds no assumptions.

Worker 357 extracts the theorem, prefixes its namespace with
`Langlands.NYLL`, converts it to a `def` returning `Prop` with suffix
`Statement`, and omits the source theorem proof. The pure definition needs
no `noncomputable section`. Comments and whitespace are adjusted. The source's
whole `Degree.Fields` import is replaced by the published
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidueExtension.ResidueDegreeDefinitions`,
which supplies the exact relative and absolute numerical invariants by
Lean name. No construction, instance, or replacement theorem is introduced.
This target does not depend on the normalized-degree map or on the two
field-image proofs required for that map's construction.

Focused `lean_check` compilation and exact declaration inspection in
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` succeeded without warnings;
the inspection reports `statement_returns_prop: true` and a single universe
parameter. This is a target for separate proof work, not a proof or independent
acceptance of the source theorem.

The original copyright and author header is retained. See
`licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).
This support target supplies no host class-formation or reciprocity theorem.
