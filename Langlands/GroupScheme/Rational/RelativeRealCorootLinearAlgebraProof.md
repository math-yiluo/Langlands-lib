# Proof of the assembled real coroot linear algebra (Renard V.3.7, V.3.12, V.3.13)

Module
`Langlands.GroupScheme.Rational.RelativeRealCorootLinearAlgebraProof`, namespace
`Langlands.GroupScheme`.

The theorem `Langlands.GroupScheme.relativeRealCorootLinearAlgebra.{u}` has type
exactly `Langlands.GroupScheme.RelativeRealCorootLinearAlgebraStatement.{u}`. That
statement is defined in the unchanged module
`Langlands.GroupScheme.Rational.RelativeRealCorootStatements`.

## What the proof does

By definition, `RelativeRealCorootLinearAlgebraStatement.{u}` is the conjunction

`RelativeRealSimpleRootBasisStatement.{u} ∧ RelativeRealCorootStatement.{u} ∧
RelativeFundamentalWeightStatement.{u} ∧ StandardLeviRealDecompositionStatement.{u}`.

The proof is the anonymous constructor of four published theorems, in this
order. Each theorem has exactly the type of its component, at the same universe
parameter `u`:

| Component | Published theorem | Module |
| --- | --- | --- |
| `RelativeRealSimpleRootBasisStatement` | `relativeRealSimpleRootBasis` | `Langlands.GroupScheme.Rational.RelativeRealSimpleRootBasisProof` |
| `RelativeRealCorootStatement` | `relativeRealCoroot` | `Langlands.GroupScheme.Rational.RelativeRealCorootProof` |
| `RelativeFundamentalWeightStatement` | `relativeFundamentalWeight` | `Langlands.GroupScheme.Rational.RelativeFundamentalWeightProof` |
| `StandardLeviRealDecompositionStatement` | `standardLeviRealDecomposition` | `Langlands.GroupScheme.Rational.StandardLeviRealDecompositionProof` |

The module imports the target module and these four proof modules by Lean name.
It adds no other declarations, and it changes none of the imported files. All of
the mathematics is in the four component proofs and their Markdown files. This
module only pairs them, and it proves nothing beyond the target conjunction. The
theorem depends only on the axioms `propext`, `Classical.choice` and `Quot.sound`.

## Scope of the proved statement

The meaning of the statement and its comparison with the source are given in the
target's Markdown, [RelativeRealCorootStatements.md](RelativeRealCorootStatements.md).
The source is David Renard, *Représentations des groupes réductifs p-adiques*,
French edition dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`: V.3.7, V.3.12 and V.3.13,
printed pp.110–113 / PDF pp.116–119. The proved statement keeps all of the target's
qualifications:

- **Arbitrary fields.** All four components are stated for every field `k`, a
  connected reductive group scheme over `Spec k` and a maximal split torus. The
  book works over a nonarchimedean local field.
- **Supplied reflection data.** The coroots come from integral reflection data
  `D : RelativeRootReflectionData i`, and every component that uses coroots holds
  for every such `D`. The existence of reflection data is not part of this
  statement.
- **Ambient annihilator models.** For a standard Levi subgroup with simple roots
  `J`, the spaces `𝔞_M` and `𝔞^*_M` are the root annihilator and the coroot
  annihilator of `J` inside `𝔞_∅` and `𝔞^*_∅`, as in V.3.13. They are not identified
  here with the real spaces of the split component `A_M`.
- **Corrected V.3.13 (source issue I4).** The pieces `(𝔞^L_M)^*` and `𝔞^L_M` are the
  parts of `𝔞^*_M` and `𝔞_M` inside the span of the roots, resp. coroots, of `K`.
  They are spanned by the projections of the roots, resp. coroots, of `K ∖ J`. The
  printed definition by the roots of `K ∖ J` themselves is false in general.
- **Every invariant scalar product.** Invariant scalar products exist. The coroot
  formula and the orthogonality clauses hold for every invariant scalar product, not
  only for one fixed product.
- **Minimal parabolic.** The root-system clauses of V.3.7 are stated only for the
  maximal split torus `A_∅`, the split component of the minimal Levi subgroup. They
  cover both the possibly nonreduced system of all relative roots and the reduced
  system of indivisible roots. The simple roots of the minimal standard parabolic,
  used in the other three components, are fixed by a generic cocharacter `ν`.
