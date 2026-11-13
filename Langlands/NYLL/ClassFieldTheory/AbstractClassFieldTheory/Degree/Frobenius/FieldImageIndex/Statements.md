# NYLL M011.002–003: targets for the index of the additive degree image

This module extracts two public theorem signatures of Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Frobenius.lean` at
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`d99a9993cdb5685118cd9b88a45c0a4e46aee57346e72566be042091bb5daa07`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable original is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

Both targets are Prop-valued definitions with prefix
`Langlands.NYLL.ClassFormation.DegreeData`.

| Unit | Source signature lines | Original theorem after `ClassFormation.DegreeData.` | Adapted target |
| --- | --- | --- | --- |
| M011.002 | 33–35 | `fieldImageAdd_index` | `fieldImageAdd_indexStatement` |
| M011.003 | 42–45 | `fieldImageAdd_eq_mulNat_range` | `fieldImageAdd_eq_mulNat_rangeStatement` |

## The objects

All data are the actual published source definitions; no replacement degree
datum, image, quotient or multiplication map is introduced.

- `D : DegreeData G` (M010.002) is the source degree datum on a group `G`
  with a topology.
- `K : FiniteResidueAbstractField D` (M010.021) bundles a closed subgroup
  `K.field : ClosedSubgroup G` with finiteness of the actual residue quotient
  `D.residueQuotient K.field`.
- `D.fieldImageAdd K.field` (M011.001) is the image `d(G_K)` of the field
  under the degree map, written as an additive subgroup of `ZHat` by Mathlib's
  `Subgroup.toAddSubgroup'` applied to `D.fieldImage K.field`.
- `K.residueDegree : ℕ+` (M010.025) is the positive residue degree
  `Nat.card (D.residueQuotient K.field)`; the targets use its coercion to `ℕ`.
- `zHatMulNat n` (M009.002) is multiplication by `n` on the closure model
  `ZHat` (M008.008) of the profinite integers, a continuous additive monoid
  homomorphism.

## Statements

`fieldImageAdd_indexStatement (D : DegreeData G) (K : FiniteResidueAbstractField D) : Prop`
is

```lean
(D.fieldImageAdd K.field).index = (K.residueDegree : ℕ)
```

The left side is Mathlib's natural-number index `AddSubgroup.index` of the
additive degree image in `ZHat`. The statement asserts that this index equals
the field's residue degree `f_K`.

`fieldImageAdd_eq_mulNat_rangeStatement (D : DegreeData G) (K : FiniteResidueAbstractField D) : Prop`
is

```lean
D.fieldImageAdd K.field =
  (zHatMulNat (K.residueDegree : ℕ)).toAddMonoidHom.range
```

an equality of additive subgroups of `ZHat`: the additive degree image is
`f_K ℤ̂`, the range of multiplication by the residue degree.

Both targets have the source section's implicit `G`, written `Type*` and so
giving one universe parameter, followed by the instance binders `[Group G]`
and `[TopologicalSpace G]` (source line 23), then explicit `D` and `K`, in
source order. No profiniteness, closedness or other hypothesis is added. The
finiteness of the residue quotient enters only through `K`.

## Modifications

Worker 5264 makes these modifications:

- Extract only the two theorem signatures, with the surrounding namespaces,
  the source's noncomputable section (source line 21) and its variable
  declaration (line 23). Omit the proofs (source lines 36–39 and 46–48), the
  theorem-only `@[simp]` attribute of M011.002 (line 32) and all other source
  declarations.
- Prefix the namespace `ClassFormation` with `Langlands.NYLL` and append
  `Statement` to each theorem name. Each theorem's conclusion becomes the body
  of a `Prop`-valued definition with the same parameters.
- Rephrase the docstrings as target descriptions that keep the source wording.
- Replace the source import `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields`
  with these published modules:
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.Definitions`
  (`fieldImageAdd`),
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidue.Definitions`
  (`FiniteResidueAbstractField` and `residueDegree`),
  `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.U002.Definitions`
  (`zHatMulNat`), and `Mathlib.GroupTheory.Index`.
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The module supplies no proofs. Proofs of the two targets are separate units.
In the source, the proof of M011.003 uses M011.002 and the published
classification target M009.013,
`zHatAddSubgroup_eq_mulNat_range_of_index_eqStatement`.

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
