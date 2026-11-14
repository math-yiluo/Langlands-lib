# NYLL M011.019: naturality of the normalized degree along a finite extension

This module extracts one public theorem signature of Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Frobenius.lean` at
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`d99a9993cdb5685118cd9b88a45c0a4e46aee57346e72566be042091bb5daa07`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable original is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

| Unit | Source signature lines | Original theorem | Adapted target |
| --- | --- | --- | --- |
| M011.019 | 258–265 | `ClassFormation.DegreeData.frobeniusRestrictionNaturality_normalizedDegree` | `Langlands.NYLL.ClassFormation.DegreeData.frobeniusRestrictionNaturality_normalizedDegreeStatement` |

Lines 258–259 are the source docstring and lines 260–265 the signature. The
proof (source lines 266–276) is omitted.

## The objects

All data are the actual published source definitions.

- `D : DegreeData G` (M010.002) is the source degree datum, with continuous
  surjective degree homomorphism `D.degree : G →ₜ* ZHatMul`, where
  `ZHatMul = Multiplicative ZHat` (M010.001).
- `E : FiniteResidueAbstractExtension D` (M010.111) is a finite extension
  `L|K` of abstract fields with finite residue quotients: its top endpoint
  `E.field` and base endpoint `E.base` are `FiniteResidueAbstractField D`
  (M010.021), `E.below : E.field.field.toSubgroup ≤ E.base.field.toSubgroup`
  is the inclusion `G_L ≤ G_K`, and the relative quotient is finite.
- `E.residueDegree : ℕ+` (M010.116, module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidueExtension.ResidueDegreeDefinitions`)
  is the relative residue degree `f_{L|K}`.
- `D.normalizedDegree K : K.field.toSubgroup →ₜ* ZHatMul` (M011.006, module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Definitions`)
  is the normalized degree `d_K = (1 / f_K) d`.
- `Subgroup.inclusion E.below : E.field.field.toSubgroup →* E.base.field.toSubgroup`
  is Mathlib's inclusion homomorphism of subgroups.

## Statement

`frobeniusRestrictionNaturality_normalizedDegreeStatement (D : DegreeData G) (E : FiniteResidueAbstractExtension D) (l : E.field.field.toSubgroup) : Prop`
is

```lean
(D.normalizedDegree E.base (Subgroup.inclusion E.below l)).toAdd =
  (E.residueDegree : ℕ) •
    (D.normalizedDegree E.field l).toAdd
```

that is, for `l ∈ G_L`, `d_K(l) = f_{L|K} · d_L(l)` in the additive group
`ZHat`. This is the commutative square relating the normalized degree maps of
`K` and `L`.

The target has the source section's implicit `G : Type*` (one universe
parameter) followed by the instance binders `[Group G]` and
`[TopologicalSpace G]` (source line 23), then the explicit binders `D`, `E`
and `l`, in source order. No hypothesis is added.

## Modifications

Worker 5264 makes these modifications:

- Extract only this theorem signature, with the surrounding namespaces, the
  source's noncomputable section (source line 21) and its variable declaration
  (line 23). Omit the proof and all other source declarations.
- Prefix the namespace `ClassFormation` with `Langlands.NYLL` and append
  `Statement` to the theorem name. The theorem's conclusion becomes the body of
  a `Prop`-valued definition with the same parameters.
- Prefix the source docstring with "Target:".
- Replace the source import `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields`
  with two focused published modules: the normalized-degree definitions module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Definitions`
  (for `normalizedDegree`, and transitively the degree datum and finite-residue
  fields) and
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteResidueExtension.ResidueDegreeDefinitions`
  (for `FiniteResidueAbstractExtension` and its `residueDegree`).
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The module supplies no proof. The proof of this target is a separate unit. In
the source it uses M009.005 `zHatMulNat_injective`, M011.008
`residueDegree_nsmul_normalizedDegree` and M011.017
`FiniteResidueAbstractExtension.residueDegree_mul_absoluteResidueDegree`.

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
