# Geometric relative dimension under rational isomorphism

`Langlands.AbelianScheme.RationalIsoRelativeDimensionStatement` is a
universe-polymorphic proposition with the following content. For any scheme
`S`, actual abelian schemes `B` and `B'` over `S`, and isomorphism

```text
e : (rationalization S).obj B ≅ (rationalization S).obj B',
```

every natural number `g` satisfies

```text
B.HasRelativeDimension g ↔ B'.HasRelativeDimension g.
```

The input is an actual categorical isomorphism, with a rational homomorphism,
an inverse and both composition identities. The published rational category
has Hom groups `ℚ ⊗[ℤ] (B ⟶ B')`, formed from the homomorphisms of the actual
commutative group schemes. The conclusion uses the published abbreviation
`HasRelativeDimension`: it means `SmoothOfRelativeDimension g` for the
actual structure morphism of the abelian scheme. Mathlib defines this
property through affine standard smooth charts of the specified relative
dimension.

The base is arbitrary, including disconnected, nonreduced and empty
schemes, and schemes in positive or mixed characteristic. There is no
assumption that either abelian scheme has a constant dimension globally.
The conclusion transports each supplied constant-dimension property; it
does not assert that some such number exists. On the empty base the
covering-based relative-dimension properties are vacuous. No nonempty-base
uniqueness assertion is made.

## Sources and derived scope

This is a derived statement for the geometric prerequisite needed when a
dimension condition is placed on Harris–Taylor rational-isogeny classes.
It is not a verbatim arbitrary-base theorem from either cited passage.

Harris and Taylor, *The Geometry and Cohomology of Some Simple Shimura
Varieties* (2001), printed page 18 / PDF page 26, define an isogeny of
abelian schemes to be an invertible element of
`Hom(A,A') ⊗[ℤ] ℚ`. The published tensor-commutation equivalence identifies
that orientation with the rational Hom groups used here. Their moduli
problem in III.1, printed page 91 / PDF page 99, prescribes dimension
`d n²` and identifies objects by such rational isogenies. That problem
uses connected, locally noetherian schemes over the indicated number
field. The present target isolates dimension preservation and extends its
base scope; it makes no representability claim.

Registered source:
`harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.

Milne, *Abelian Varieties* (1986 article, corrected author revision 2022),
Section 8, Proposition 8.1, printed/PDF page 12, proves that an isogeny of
abelian varieties over a field preserves dimension, and identifies
isogenies with finite, flat, surjective homomorphisms. Theorem 8.2,
printed/PDF page 13, proves that multiplication by a positive integer
is an isogeny, in every characteristic. Section 20, printed/PDF page 42,
defines abelian schemes over arbitrary schemes and identifies their
geometric fibres as abelian varieties. These passages motivate reduction
of this target to geometric fibres; Proposition 8.1 alone does not prove
the stated arbitrary-base chart property.

Registered source: `milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The registered errata snapshot
`milne-abelian-varieties-1986-errata-2026-10-25`, SHA256
`e206fed351fc3d740772f2c1d3275e877552393fafc1644c6c2f38fedd1d9a55`,
states that its listed corrections are incorporated in the corrected
author version. None changes the cited results.

## Remaining proof obligations

A fibrewise proof can transport the rational isomorphism along geometric
base change. Over each resulting field, clearing denominators, including
the integral relations represented by rational equalities, should give
integral homomorphisms whose two composites are multiplication by a
common nonzero integer. Finiteness of multiplication kernels and
surjectivity of multiplication then give a field isogeny and equality of
the fibre dimensions. Connecting those fibre dimensions with Mathlib's
affine-chart definition of `SmoothOfRelativeDimension` is a further
geometric obligation. Neither the base-change construction nor that
comparison is assumed as an input to this proposition.

In positive characteristic an isogeny's differential need not be an
isomorphism. Thus a characteristic-zero Lie comparison does not by
itself prove this target over the stated bases. The companion Lean file
defines only the proposition, without a proof, an assumed dimension
equality, or a selected geometric comparison.
