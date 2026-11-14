# NYLL M011.008–010: targets for the normalized degree map

This module extracts three public theorem signatures of Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Frobenius.lean` at
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`d99a9993cdb5685118cd9b88a45c0a4e46aee57346e72566be042091bb5daa07`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable original is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

All targets are Prop-valued definitions with prefix
`Langlands.NYLL.ClassFormation.DegreeData`.

| Unit | Source signature lines | Original theorem after `ClassFormation.DegreeData.` | Adapted target |
| --- | --- | --- | --- |
| M011.008 | 112–115 | `residueDegree_nsmul_normalizedDegree` | `residueDegree_nsmul_normalizedDegreeStatement` |
| M011.009 | 121–123 | `normalizedDegree_surjective` | `normalizedDegree_surjectiveStatement` |
| M011.010 | 141–143 | `normalizedDegree_ker` | `normalizedDegree_kerStatement` |

## The objects

All data are the actual published source definitions.

- `D : DegreeData G` (M010.002) is the source degree datum, with continuous
  surjective degree homomorphism `D.degree : G →ₜ* ZHatMul`, where
  `ZHatMul = Multiplicative ZHat` (M010.001).
- `K : FiniteResidueAbstractField D` (M010.021) is a closed subgroup
  `K.field` with finite residue quotient, and `K.residueDegree : ℕ+` (M010.025)
  is its positive residue degree `f_K`.
- `D.normalizedDegree K : K.field.toSubgroup →ₜ* ZHatMul` (M011.006, in the
  sibling module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Definitions`)
  is the normalized degree `d_K = (1 / f_K) d`.
- `D.fieldInertiaWithin K.field : Subgroup K.field.toSubgroup` (M010.014) is
  the inertia group `I_K`, the kernel of the restricted degree map on `G_K`.

## Statements

`residueDegree_nsmul_normalizedDegreeStatement (D : DegreeData G) (K : FiniteResidueAbstractField D) (k : K.field.toSubgroup) : Prop`
is

```lean
(K.residueDegree : ℕ) • (D.normalizedDegree K k).toAdd =
  (D.degree k.1).toAdd
```

the defining identity `f_K d_K(k) = d(k)` in the additive group `ZHat`.

`normalizedDegree_surjectiveStatement (D : DegreeData G) (K : FiniteResidueAbstractField D) : Prop`
is

```lean
Function.Surjective (D.normalizedDegree K)
```

that is, `d_K : G_K → ℤ̂` is onto.

`normalizedDegree_kerStatement (D : DegreeData G) (K : FiniteResidueAbstractField D) : Prop`
is

```lean
(D.normalizedDegree K).toMonoidHom.ker = D.fieldInertiaWithin K.field
```

an equality of subgroups of `K.field.toSubgroup`: the kernel of `d_K` is the
inertia group `I_K`.

All three targets have the source section's implicit `G : Type*` (one universe
parameter) followed by the instance binders `[Group G]` and
`[TopologicalSpace G]` (source line 23), then the explicit binders `D`, `K`
and, for M011.008, `k`, in source order. No hypothesis is added.

## Modifications

Worker 5264 makes these modifications:

- Extract only the three theorem signatures, with the surrounding namespaces,
  the source's noncomputable section (source line 21) and its variable
  declaration (line 23). Omit the proofs (source lines 116–117, 124–138 and
  144–160) and all other source declarations.
- Prefix the namespace `ClassFormation` with `Langlands.NYLL` and append
  `Statement` to each theorem name. Each theorem's conclusion becomes the body
  of a `Prop`-valued definition with the same parameters.
- Rephrase the docstrings as target descriptions that keep the source wording.
- Replace the source import `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields`
  with the sibling definitions module
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Definitions`,
  which supplies `normalizedDegree` and transitively the degree datum,
  finite-residue fields and `fieldInertiaWithin`.
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The module supplies no proofs. Proofs of the three targets are separate units.
In the source, the proof of M011.008 is M009.017 `zHatMulNat_zHatDivide`; the
proofs of M011.009 and M011.010 use M011.008, M009.005
`zHatMulNat_injective`, and, for M011.009, M011.003
`fieldImageAdd_eq_mulNat_range`.

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
