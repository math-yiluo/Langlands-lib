# NYLL M011.001: the additive degree image

This file adapts Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Frobenius.lean`,
lines 27–29 (declaration at line 28), at pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`d99a9993cdb5685118cd9b88a45c0a4e46aee57346e72566be042091bb5daa07`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable original is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

| Original name | Adapted name |
| --- | --- |
| `ClassFormation.DegreeData.fieldImageAdd` (M011.001) | `Langlands.NYLL.ClassFormation.DegreeData.fieldImageAdd` |
| `ClassFormation.DegreeData` (dependency M010.002) | `Langlands.NYLL.ClassFormation.DegreeData` |
| `ClassFormation.DegreeData.fieldImage` (dependency M010.010) | `Langlands.NYLL.ClassFormation.DegreeData.fieldImage` |
| `ClassFormation.ZHat` (dependency M008.008) | `Langlands.NYLL.ClassFormation.ZHat` |

The complete telescope is, for an arbitrary universe `u`,

```lean
∀ {G : Type u} [Group G] [TopologicalSpace G]
  (D : Langlands.NYLL.ClassFormation.DegreeData G)
  (K : ClosedSubgroup G),
  AddSubgroup Langlands.NYLL.ClassFormation.ZHat
```

The implicit carrier, the two instance binders, and the explicit `D` and `K`
are retained in source order. The source's `Type*` introduces this single
universe parameter. No finite residue degree, profiniteness, or topological
group hypothesis is imposed.

The body is exactly `Subgroup.toAddSubgroup' (D.fieldImage K)`.
The published `fieldImage` is the actual range of the restricted continuous
degree homomorphism, as a subgroup of `ZHatMul = Multiplicative ZHat`.
Mathlib's existing `Subgroup.toAddSubgroup'` converts that subgroup to an
additive subgroup of the same profinite-integer model. Thus the carrier
consists of those `z : ZHat` for which `Multiplicative.ofAdd z` belongs to
`D.fieldImage K`. The subgroup laws come from the same Mathlib conversion
as in the source; no replacement construction or new instance is introduced.

Worker 199 makes these modifications:

- Extract only M011.001 and its surrounding namespace, variable declaration
  (source line 23), and noncomputable section (line 21). Omit all later source
  declarations and narrow the module documentation to this definition.
- Prefix the source namespace `ClassFormation` with `Langlands.NYLL`.
  The nested namespace `DegreeData`, declaration spelling, docstring,
  telescope, result type and construction body are unchanged.
- Replace the original import
  `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields` with the
  published focused module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.Definitions`.
  It supplies the actual source degree datum and image, their profinite-integer
  dependency and the required Mathlib subgroup conversion.
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
This is the additive image data alone. The later index, normalized degree and
Frobenius assertions remain separate source units; this definition establishes
no host class-formation or reciprocity comparison.
