# Transitivity of actual normalized opposite Jacquet quotients

Author: Worker 430.

`Langlands.Parabolic.NormalizedOppositeRefinementTransitivityStatement`
is a closed proposition definition. It states a pointwise representation
equivalence between the actual iterated opposite quotient and the actual
composed opposite quotient. This file contains no proof of that proposition.

## Groups, carriers, and the prescribed map

Let `F : PadicField p` and let `T : F.TopologicalData`. For any rank `n`,
ordered block shape `B : BlockShape n`, refinement `S : BlockRefinement B`,
and complex representation `A` of `GeneralLinear n F.Carrier`, put

```text
O = CuspidalJacquetMultiplicity.oppositeJacquet T B A.
```

The representation `O` is on the actual quotient of `A` by the span of the
outer lower-radical differences. Its group is the actual product Levi
`B.Levi F.Carrier`, obtained using the published `B.leviEquiv`.
The next quotient uses `Geometric.refinedOppositeUnipotent F.Carrier B S`,
the product of the inner lower radicals in that product Levi.

The target instead quotients `A` directly by
`Parabolic.composedOppositeUnipotent F.Carrier B S`. This is the ambient
preimage of the inner lower radical under the outer opposite Levi
projection. It contains the whole outer lower radical and the embedded
inner lower radical. Both resulting representations have group
`Geometric.refinedLevi F.Carrier B S`, the existing actual common refined
Levi subgroup.

The statement supplies an actual `Representation.Equiv`, hence an
invertible complex-linear map that intertwines those normalized actions.
It prescribes its value on every original vector:

```text
E ([[v]]) = [v].
```

Here the first class is `Jacquet.mk` for the outer opposite radical,
the second is `refinedOppositeJacquetMk`, and the direct class is
`composedOppositeJacquetMk`. The representative formula specifies the
direction of the equivalence. There is no supplied transitivity map,
subgroup equality, normalization certificate, or classification theorem.
The conclusion is pointwise in `A`; it does not assert a categorical
natural isomorphism.

## Normalization

Both quotient actions use the published actual opposite normalization.
The outer quotient multiplies its raw Levi action by
`T.leviHalfModulus B`, the canonical positive half of the upper full
modulus. The inner quotient multiplies by
`T.refinedLeviHalfModulus B S`. Each is the inverse half of the
corresponding opposite full modulus.

The direct quotient uses `T.composedLeviHalfModulus B S`. Its upper full
character is defined as the restricted outer full character times the
inner full character, and the published positive-half product identity
gives the corresponding product of halves.

A later proof must show that the outer character is trivial on the
actual inner opposite radical and factors through the actual inner
opposite Levi projection. On the common refined Levi the outer scalar
is its restriction; multiplying by the inner scalar then gives exactly
the composed scalar. These compatibility assertions are proof
obligations, not hypotheses of this statement. The upper-only Jacquet
transitivity proposition is a separate assertion.

## Scope and provenance

The field universe `uF` and representation-carrier universe `uV` are
independent. All quotient carriers remain in `uV`. The quantifiers include
rank zero and the empty block shape. No smoothness, admissibility,
irreducibility, finite length, positive rank, proper-parabolic, or
nonzero-representation condition is added.

This is an internal derived refinement of the published concrete
constructions in `OppositeRefinementDefinitions`,
`OppositeRefinementFunctors`, `RefinementComposition`, and the bundled
outer quotient in `CuspidalJacquetMultiplicityStatement`. The intended
algebraic argument uses the universal property of coinvariants twice
and the actual opposite split projection, then checks normalized
equivariance on representatives. The equivalence is a later proof
target; the definitions imported here do not by themselves prove it.

The source motivation is A. J. Silberger, *The Langlands quotient theorem
for p-adic groups*, Math. Ann. **236** (1978), 95–104, section 2, printed
p.97 (PDF page 3). Source
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`,
retained at
`/home/taskhub/pilot/literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`,
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
Worker 430 reread that page and its image for this contribution. It
recalls transitivity of the Jacquet functor and records the opposite
normalization convention. The exact Lean quotient presentations, all-rank
scope, independent universes, and representative formula are internal
specializations, rather than verbatim assertions in that source.
There was no `notes/errata` directory at the Library base inspected for
this contribution.

This proposition supplies no flattened-coordinate comparison,
Haar-scaling interpretation of the explicit modulus, exactness,
multiplicity comparison, recovery, or classification theorem.
