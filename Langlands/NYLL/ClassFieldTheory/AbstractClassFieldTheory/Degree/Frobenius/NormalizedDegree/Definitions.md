# NYLL M011.004 and M011.006: the normalized degree map

This file adapts two definitions of Naganori Yamaguchi's
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Frobenius.lean` at
pinned commit `fbd320cd8b1b06487c58227e92eb135794267709` of
`n-yamaguchi-0729/ClassFieldTheory`. The original file SHA-256 is
`d99a9993cdb5685118cd9b88a45c0a4e46aee57346e72566be042091bb5daa07`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`,
content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The readable original is in the project's literature collection under
`External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.

| Unit | Source lines (declaration line) | Original name after `ClassFormation.DegreeData.` | Adapted name |
| --- | --- | --- | --- |
| M011.004 | 50–57 (51) | `restrictedDegreeInMulNatRange` | `Langlands.NYLL.ClassFormation.DegreeData.restrictedDegreeInMulNatRange` |
| M011.006 | 66–100 (67) | `normalizedDegree` | `Langlands.NYLL.ClassFormation.DegreeData.normalizedDegree` |

## The objects

All data are the actual published source definitions; no replacement degree
datum, field, residue degree or division map is introduced.

- `D : DegreeData G` (M010.002) is the source degree datum: a continuous
  surjective homomorphism `D.degree : G →ₜ* ZHatMul`, where
  `ZHatMul = Multiplicative ZHat` (M010.001) and `ZHat` (M008.008) is the
  closure model of the profinite integers.
- `K : FiniteResidueAbstractField D` (M010.021) bundles a closed subgroup
  `K.field : ClosedSubgroup G` with finiteness of its residue quotient, and
  `K.residueDegree : ℕ+` (M010.025) is its positive residue degree `f_K`.
- `D.fieldImage K.field` (M010.010) is the range of the restricted degree
  `D.restrictedDegree K.field : K.field.toSubgroup →ₜ* ZHatMul` (M010.008),
  and `D.fieldImageAdd K.field` (M011.001) is that image written additively.
- `zHatMulNat n` (M009.002) is multiplication by `n` on `ZHat`, and
  `zHatDivide n hn` (M009.016) is the continuous additive inverse of
  multiplication by `n > 0` on its range `n ℤ̂`.

## Telescopes

Both definitions have the source section's implicit `G : Type*` (one universe
parameter) followed by the instance binders `[Group G]` and
`[TopologicalSpace G]` (source line 23), then the explicit binders below, in
source order. No hypothesis is added.

```lean
Langlands.NYLL.ClassFormation.DegreeData.restrictedDegreeInMulNatRange
    (D : DegreeData G) (K : FiniteResidueAbstractField D)
    (k : K.field.toSubgroup) :
    (zHatMulNat (K.residueDegree : ℕ)).toAddMonoidHom.range

Langlands.NYLL.ClassFormation.DegreeData.normalizedDegree
    (D : DegreeData G) (K : FiniteResidueAbstractField D) :
    K.field.toSubgroup →ₜ* ZHatMul
```

## Constructions

`D.restrictedDegreeInMulNatRange K k` is the additive value
`(D.degree k.1).toAdd : ZHat`, packaged as an element of the additive subgroup
`f_K ℤ̂`, the range of `zHatMulNat (K.residueDegree : ℕ)`. The membership proof
is the source proof. It rewrites `f_K ℤ̂` backwards to `D.fieldImageAdd K.field`
by the published theorem M011.003
`Langlands.NYLL.ClassFormation.DegreeData.fieldImageAdd_eq_mulNat_range`, which
proves `fieldImageAdd_eq_mulNat_rangeStatement D K`. The rewrite works through
that Prop-valued target definition unchanged. It then identifies membership in
the additive image with `D.degree k.1 ∈ D.fieldImage K.field` by `change`, and
uses `k` itself as the witness.

`D.normalizedDegree K` is the continuous homomorphism `d_K = (1 / f_K) d` of the
source. Its function sends `k` to
`Multiplicative.ofAdd (zHatDivide f_K _ (D.restrictedDegreeInMulNatRange K k))`,
the unique `x : ZHat` with `f_K • x = d(k)`, viewed in `ZHatMul`. The fields
`map_one'` and `map_mul'` are the source proofs. They show that
`restrictedDegreeInMulNatRange` sends `1` to `0` and products to sums, because
`D.degree` is a monoid homomorphism, and then use additivity of `zHatDivide`.
`continuous_toFun` composes the continuity of `zHatDivide` with
`Continuous.subtype_mk` applied to the continuity of
`D.restrictedDegree K.field`.

The targets M011.008 (`f_K d_K = d`), M011.009 (surjectivity) and M011.010
(the kernel is the inertia group) are stated in the sibling module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.NormalizedDegree.Statements`.
The source's `rfl` lemmas M011.005 `restrictedDegreeInMulNatRange_coe` and
M011.007 `normalizedDegree_apply_toAdd` are not part of this module.

## Modifications

Worker 5264 makes these modifications:

- Extract only M011.004 and M011.006, with the surrounding namespaces, the
  source's noncomputable section (source line 21) and its variable
  declaration (line 23). Omit all other source declarations and narrow the
  module documentation to these definitions.
- Prefix the source namespace `ClassFormation` with `Langlands.NYLL`. The
  declaration names, docstrings, telescopes, result types and construction
  bodies, including the proof terms inside them, are unchanged.
- Replace the source import `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields`
  with two published modules:
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Frobenius.FieldImageIndex.U003.Proofs`
  contains the proof of M011.003 that the body of M011.004 uses, and it
  transitively imports the degree datum, finite-residue fields, `fieldImage`,
  `fieldImageAdd` and `zHatMulNat`;
  `Langlands.NYLL.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger.Divide.Definitions`
  contains `zHatDivide`, which the body of M011.006 uses.
- Retain the original copyright, Apache-2.0 and author header, and add the
  explicit modification record in the Lean module documentation.

The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` are retained,
with SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`.
