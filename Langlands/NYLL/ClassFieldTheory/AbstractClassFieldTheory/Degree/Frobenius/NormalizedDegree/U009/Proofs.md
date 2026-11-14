# NYLL M011.009: surjectivity of normalized degree

The theorem `Langlands.NYLL.ClassFormation.DegreeData.normalizedDegree_surjective`
proves exactly
`Langlands.NYLL.ClassFormation.DegreeData.normalizedDegree_surjectiveStatement D K`.
The implicit parameters are `G : Type*`, `[Group G]` and
`[TopologicalSpace G]`; the explicit parameters are `D : DegreeData G`,
`K : FiniteResidueAbstractField D`, in source order.

`D.normalizedDegree K : K.field.toSubgroup →ₜ* ZHatMul` is the actual
normalized degree map, where `ZHatMul = Multiplicative ZHat` and
`K.residueDegree : ℕ+` is the positive residue degree.

## Implemented proof and dependencies

The conclusion is `Function.Surjective (D.normalizedDegree K)`.
For an arbitrary `z : ZHatMul`, the proof uses the published M011.003
`D.fieldImageAdd_eq_mulNat_range K` to put
`(K.residueDegree : ℕ) • z.toAdd` in the actual additive degree image.
The same membership, written multiplicatively, supplies
`k : K.field.toSubgroup` with
`D.degree k.1 = Multiplicative.ofAdd ((K.residueDegree : ℕ) • z.toAdd)`.
It remains to prove `D.normalizedDegree K k = z`.

After `Multiplicative.ext`, the proof applies M009.005
`zHatMulNat_injective K.residueDegree.property`, multiplying both sides
by the positive residue degree. M011.008
`D.residueDegree_nsmul_normalizedDegree K k` rewrites the left side to
the raw degree, and `congrArg Multiplicative.toAdd hk` is the required
equality. The initial `intro z` unfolds the named target.

The only direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.U008.Proofs`.
It supplies M011.008 and transitively the unchanged statement, the
actual degree constructions, M011.003 and M009.005.

## Source and modifications

Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Frobenius.lean`,
lines 121–138, source unit M011.009. The file SHA-256 is
`d99a9993cdb5685118cd9b88a45c0a4e46aee57346e72566be042091bb5daa07`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable source root is
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

Worker 499 extracts this theorem, adds the `Langlands.NYLL` namespace
prefix and focused imports, and changes the conclusion to the exact
named Statement target without changing the parameters or binder kinds.
The proof body is unchanged from the original.
The focused adaptation and prior compilation were supplied by Worker 5264.
The source docstring is shortened to describe surjectivity.

The original 2026 copyright and author header (Naganori Yamaguchi,
assisted by OpenAI Codex) is retained. The existing Apache-2.0
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain applicable and
unchanged. Their SHA-256 values are respectively
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.

This proof concerns the NYLL abstract degree datum and discharges no host
class-formation, cup, transfer, Tate or reciprocity target.
