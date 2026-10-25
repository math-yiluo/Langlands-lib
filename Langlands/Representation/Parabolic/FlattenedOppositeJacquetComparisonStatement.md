# The actual flattened and composed opposite Jacquet quotients

`Langlands.Parabolic.FlattenedOppositeJacquetComparisonStatement` bundles
two closed proposition definitions. This file supplies their statements;
it supplies no proof.

For every commutative ring `K`, rank `n`, ordered block shape `B` and
ordered refinement `S`,
`FlattenedOppositeUnipotentComparisonStatement` asserts the literal
subgroup equality

```text
Parabolic.composedOppositeUnipotent K B S =
  (B.flatten S).oppositeUnipotentSubgroup K.
```

Both sides are subgroups of the same actual matrix group
`GeneralLinear n K`. The left side is the inverse image of the inner
opposite radical under the outer opposite Levi projection, included into
the ambient matrix group. The right side is the standard opposite
radical of the ordered flattened shape. There is no conjugation, free
permutation or supplied subgroup equality.

For a p-adic field `F`, its compatible topological datum `T`, and any
complex representation `A` of the ambient general linear group, put
`C = B.flatten S` and
`e = Geometric.flattenedLeviEquiv F.Carrier B S`. The second clause,
`FlattenedNormalizedOppositeJacquetComparisonStatement`, asserts an actual
representation equivalence

```text
Representation.Equiv
  ((T.normalizedComposedOppositeJacquet B S A.ρ).comp e.toMonoidHom)
  (CuspidalJacquetMultiplicity.oppositeJacquet T C A).ρ.
```

The constructed group equivalence `e` goes from `C.Levi F.Carrier` to the
actual refined Levi subgroup of `B.Levi F.Carrier`. Thus the source
representation is pulled back along `e` and has the same acting group as
the standard flattened target. The equivalence is required to send
`Parabolic.composedOppositeJacquetMk B S A.ρ v` to
`Jacquet.mk A.ρ (C.oppositeUnipotentSubgroup F.Carrier) v` for every
original vector `v`. Its direction and values on quotient representatives
are fixed. The statement requires invertibility and equivariance, beyond
existence of a linear surjection.

The ring universe `uK`, p-adic-field universe `uF` and representation
carrier universe `uV` are independent. Both clauses include rank zero,
unrefined shapes and zero representations. They assume no smoothness,
admissibility, nontriviality, finite length, irreducibility, modulus
comparison or classification theorem.

## Normalization and proof boundary

The two opposite Jacquet actions use the inverse half of the opposite
full modulus, equivalently the positive half of the corresponding upper
full modulus. In particular, the action on the composed quotient class
contributes `T.composedLeviHalfModulus B S (e m)`; the action on the
standard flattened class contributes `T.leviHalfModulus C m`. The
ambient matrix actions agree by the published
`Geometric.flattenedLeviEquiv_embedding`.

A future proof must establish the radical equality and compare the actual
normalizing characters. One route uses the full positive-character
identity

```text
(T.composedLeviModulus B S).comp e.toMonoidHom = T.leviModulus C
```

and the canonical positive square-root construction. This implies

```text
T.leviHalfModulus C m =
  T.leviHalfModulus B (e m).val *
    T.refinedLeviHalfModulus B S (e m).
```

The intrinsic `composedLeviHalfModulus_eq` factors the composed half
character into the two stage halves. It does not by itself identify that
character with the standard flattened one. No such comparison is supplied
as a premise here. The literal radical equality identifies the quotient
relations; it alone does not check the scalar factors in the normalized
actions.

This interface concerns composed and flattened opposite coinvariants. It
does not assert transitivity from an iterated quotient, and it is distinct
from the upper normalized flattened-to-iterated Jacquet surjection. It
supplies no occurrence, continuation, multiplicity constancy, reciprocity,
finite-length, quotient-existence or irreducible-head assertion.

## Provenance

The exact interface is internally derived from the published ordered
matrix constructions in `Geometric.FlattenedLevi` and
`Parabolic.OppositeRefinementDefinitions`, the actual quotient and
normalized action in `Parabolic.OppositeRefinementFunctors`, and the
bundled standard opposite action in
`Classification.CuspidalJacquetMultiplicityStatement`. Existing
Lean/Markdown pairs are unchanged.

Silberger, *The Langlands Quotient Theorem for p-adic Groups* (1978),
section 2, printed p.97, motivates Jacquet transitivity and the opposite
normalization. It does not state this exact coordinate presentation,
representative formula, all-rank scope or universe packaging. The retained
original is registered as
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
Worker 429 read the complete article and inspected its p.97 formula image.
No author-issued erratum was found in the retained collection.
