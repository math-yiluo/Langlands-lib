# Transitivity of the normalized opposite Jacquet quotients

Author: Worker 430.

`Langlands.Parabolic.normalizedOppositeRefinementTransitivity` proves the
unchanged Library proposition
`Langlands.Parabolic.NormalizedOppositeRefinementTransitivityStatement`.
The field universe `uF` and representation-carrier universe `uV` are
independent. The theorem applies to every rank, including zero, every
ordered block shape and refinement, and every complex representation of
the actual general linear group. It has no smoothness, admissibility,
finite-length, or irreducibility hypothesis.

For a block shape `B`, refinement `S`, and representation `A`, write
`N₀` for the outer opposite unipotent subgroup, `N₁` for
`refinedOppositeUnipotent F.Carrier B S`, and `N` for
`composedOppositeUnipotent F.Carrier B S`. The last group is the ambient
image of the preimage of `N₁` under the actual outer opposite Levi
projection. The theorem constructs an equivariant linear equivalence
from the iterated quotient to the direct quotient, with

```text
E ([[v]]) = [v]   for every v in A.
```

Both sides have the actual common group
`Geometric.refinedLevi F.Carrier B S`. The classes are the published
`Jacquet.mk`, `refinedOppositeJacquetMk`, and
`composedOppositeJacquetMk`; no replacement quotient presentation is
introduced.

## Characters on the inner radical

The private lemma `lower_determinant_one` proves that each matrix in an
actual lower block-unipotent subgroup has determinant one. It reindexes
the matrix by the block index equivalence, regards it as block triangular
for the dual order, identifies every diagonal block with the identity,
and applies the block-triangular determinant formula.

`outer_full_trivial` applies this calculation to every coarse Levi
component of an element of `N₁`. Each determinant has normalized absolute
value one, so the element lies in the norm-one Levi subgroup and the
published kernel inclusion makes the outer full modulus one.
`outer_half_trivial` then uses the published criterion for its canonical
positive half to equal one.

The helpers `outer_full_projection` and `outer_half_projection` also
prove factorization through the actual inner opposite Levi projection.
For an inner opposite-parabolic element `q`, its product with the
inverse of the section of its projection has trivial projection and
therefore lies in `N₁`. The preceding triviality and the character law
give the full-character identity. Applying the defining square-root and
complexification maps gives the half-character identity.

The private abbreviation `outer` expands the bundled outer quotient
`CuspidalJacquetMultiplicity.oppositeJacquet T B A`; it is definitionally
the same representation. `outer_mk` unfolds its normalization and proves
the representative formula

```text
outer(m)[v] = leviHalfModulus(B,m) · [A(leviEmbedding(m))v].
```

This is the positive half of the upper modulus, as required for the
opposite quotient. The implementation uses the existing inverse-half
normalization of the inverse full character.

## The two quotient maps

`firstMap` descends the direct quotient map `A → A_N` through the outer
quotient. Its invariance follows from the published inclusion `N₀ ≤ N`.
The map `forward` descends it again through the inner quotient. On an
outer class, `outer_mk` and `outer_half_trivial` remove the normalizing
scalar. The published inclusion of the embedded inner radical in `N`
then proves invariance. Both descents use `Jacquet.lift` and give the
formula `[[v]] ↦ [v]` by its representative computation rule.

For the reverse direction, `iteratedMk` is the composite of the two
actual quotient maps out of `A`. To prove it invariant under `N`,
`iteratedMk_invariant` uses membership in the opposite Levi preimage and
the actual split decomposition. It writes an element of `N` as an outer
opposite-unipotent element times the Levi embedding of an element of
`N₁`. The first quotient kills the first factor. The outer action
formula, with half-modulus one on the second factor, identifies the
remaining action with an inner radical action, which the second quotient
kills. `backward` consequently descends `iteratedMk` through the direct
quotient and has formula `[v] ↦ [[v]]`.

## Equivariance and inverses

`forwardIntertwiner` proves normalized equivariance on iterated classes.
Both quotient maps are surjective, so it suffices to check an original
vector `v`. The published inner and composed representative formulas,
`outer_mk`, and linearity reduce the equality to the scalar identity

```text
innerHalf(m) · outerHalf(m) = composedHalf(m).
```

The published `composedLeviHalfModulus_eq` supplies the product of the
restricted outer half with the inner half; commutativity of complex
scalars completes the calculation. This verifies the actual normalized
actions on the common refined Levi.

The lemma `equivalence` checks the two composite identities on
representatives, using the surjectivity of the actual quotient maps.
It packages `forwardIntertwiner` as a `Representation.Equiv` using
`IntertwiningMap.ofBijective`, which preserves its forward map. The
result therefore retains the prescribed value on every original vector.
The final theorem introduces the quantifiers of the published proposition
and applies this construction.

## Provenance and scope

This proof is an internal algebraic derivation from the published concrete
constructions in `OppositeRefinementDefinitions`,
`OppositeRefinementFunctors`, `RefinementComposition`,
`CuspidalJacquetMultiplicityStatement`, and `Jacquet.Coinvariants`.
Its proof route is the successive universal properties of coinvariants,
the actual opposite split decomposition, and the explicit character
identities described above.

The motivation recorded in the target statement is A. J. Silberger,
*The Langlands quotient theorem for p-adic groups*, Math. Ann. **236**
(1978), 95–104, section 2, printed p.97 (PDF page 3). Registered source:
`provided-5423f8a28c0b7ad5a7f9a07a3d55d399d5162a798fecd70bf11a5d75fa8b9354`;
retained file:
`/home/taskhub/pilot/literature/Silberger (1978), The Langlands quotient theorem for p-adic groups.pdf`;
SHA256 `4f437d7ee21c65e43ede0a34b9a6b274cf4d947c23ad7637976bd38fd72fdac5`.
That page recalls Jacquet transitivity and the opposite normalization.
The concrete representative formula, arbitrary algebraic representations,
all-rank scope, and independent universes are internal refinements rather
than verbatim claims attributed to that source.

The theorem establishes the pointwise transitivity assertion. Flattened
coordinates, multiplicities, relative recovery, and quotient reflection
are separate obligations.
