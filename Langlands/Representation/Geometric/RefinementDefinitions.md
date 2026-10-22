# Product-Levi refinement geometry and explicit modulus

Author: Worker 76.

This module constructs the standard parabolic geometry inside an actual product
Levi of `GL_n`. It uses exactly `BlockRefinement`, `refinedParabolic`,
`refinedLevi`, and `refinedUnipotent` from `Geometric.WeylDefinitions`.
For an ordered block shape `B` and one ordered refinement `S i` of each outer
block, the ambient group is `B.Levi R`, the product of the actual general linear
groups of the outer blocks. The three refined subgroups are the products of
the inner standard upper-block parabolics, diagonal Levi subgroups, and radicals.
The algebraic construction works over every commutative ring `R`, including
empty block shapes; the modulus construction specializes to a p-adic field.

## Projection, radical, and topology

`refinedParabolicEval` and `refinedLeviEval` evaluate in an actual inner subgroup.
`refinedLeviEquiv` explicitly identifies the nested product
`∀ i, (S i).Levi R` with the existing subgroup `refinedLevi R B S`.
It applies the published block diagonal embeddings in the forward direction
and their proved inverses in the reverse direction. Thus no block flattening
or replacement Levi is assumed.

`refinedLeviProjection` applies each published inner diagonal-block projection
and then the nested-product equivalence. Its codomain is the actual subgroup
`refinedLevi R B S`. `refinedLeviSection` is the inclusion of this subgroup into
`refinedParabolic R B S`; their composite is the identity. The homomorphism
laws follow from the component homomorphisms and the equivalence.

`refinedUnipotentRadical` is the projection kernel in the parabolic.
`mem_refinedUnipotentRadical`, `refinedLeviProjection_ker`, and
`refinedUnipotentRadical_map` prove, respectively, that its membership condition,
its preimage description, and its ambient image are exactly the previously
published product radical. The proof reduces to the inner projection kernels
and the injectivity of subgroup inclusion. Kernel normality and the normalizer
image lemma prove that the entire refined parabolic normalizes the ambient
radical. `refinedLeviNormalizer` is the resulting actual Levi homomorphism into
that normalizer, with underlying function equal to subgroup inclusion.

`refinedUnipotentPart g` is `g * section(projection(g))⁻¹`.
`refinedDecomposition` gives the unique factorization into this radical element
and a refined Levi element. Its inverse is multiplication `u * section(m)`;
the two inverse laws follow from the section and kernel identities. This is an
equivalence of types, not a claim that the parabolic is a direct-product group.

For a topological commutative ring, the coordinate evaluations are continuous.
`refinedLeviEquivContinuous` is a topological multiplicative equivalence, and
`refinedLeviProjectionContinuous`, `refinedLeviSectionContinuous`, and
`refinedLeviNormalizerContinuous` package the proved continuous homomorphisms.
These use the product and subgroup topologies, with the published continuous
inner block maps. In particular, the projection has the continuity needed for
pullback of smooth representations.

## Explicit positive character and normalization

Let `F : PadicField p`, with `p` prime, and let `T : F.TopologicalData` be
compatible topological data. All following names are in
`Langlands.PadicField.TopologicalData`.

`refinedLeviBlock B S i` extracts the nested inner Levi coordinates from an
actual refined Levi element. The full positive character is

`T.refinedLeviModulus B S m = ∏ i, T.leviModulus (S i) (refinedLeviBlock B S i m)`.

Each factor is the published explicit block modulus. If the inner block sizes
in outer block `i` are `s_(i,a)` and its inner diagonal matrices are `m_(i,a)`,
this is the finite product, over `i` and `a < b`, of

`|det m_(i,a)|_F ^ s_(i,b) / |det m_(i,b)|_F ^ s_(i,a)`.

The determinant norms use the published residue normalization. Multiplicativity
is proved by construction as a finite product of genuine homomorphisms.
`refinedParabolicModulus` inflates it through `refinedLeviProjection`.
Its section identity and triviality on the actual radical follow from the
proved projection laws.

`refinedLeviHalfModulus` is the complex embedding of the canonical positive
square root of the full character. `refinedLeviInverseHalfModulus` is Jacquet's
published canonical inverse half, definitionally the inverse of the positive
half. The value and square identities fix both the sign and magnitude of these
normalizations. `refinedParabolicHalfModulus` and
`refinedParabolicInverseHalfModulus` inflate these same characters; each has
proved section and radical identities. The positive half is the induction
convention, and the inverse half is the Jacquet convention.

Each factor kernel is open by the published block result and continuous
coordinate evaluation. Their finite intersection is open and lies in the
full-product kernel, proving that kernel open. Both half kernels equal the
full kernel. Pullback through the continuous projection proves the three
parabolic kernels open. Continuity of the full modulus follows from finite
products; continuity of both halves follows from the continuous square root,
complex embedding, and inversion on units. Inflation gives continuity on the
parabolic. The full character is independent of compatible realization by
`refinedLeviModulus_eq`. These constructions apply in particular to
`F.canonicalTopologicalData` without adding assumptions on the algebraic field.

## Provenance and scope

The original source is Bernstein and Zelevinsky, *Induced representations of
reductive p-adic groups I* (1977), source ID
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
The following original pages were read:

- Sections 2.1–2.3, printed page 446 / PDF page 7: standard parabolic triples,
  their Levi decompositions, ordered partitions for `GL_n`, and subpartitions
  describing standard Levi subgroups within another Levi.
- Sections 1.7–1.8, printed page 444 / PDF page 5: the positive conjugation
  modulus, its positive half in induction, and inverse half in Jacquet.
- Section 6.3, printed page 468 / PDF page 29: parabolic triples inside Levi
  groups arising from the geometric-lemma intersections. This motivates the
  actual-subgroup interface; the intersection identification is not asserted
  by this module.

The coordinatewise maps, kernel and normalizer proofs, factorization,
continuity, and explicit finite product are internal type-A derivations from
those definitions and the published `Group.GL.Blocks`, `Group.GL.BlockModulus`,
and `Jacquet.PositiveCharacter` constructions. The factor formula expresses
the row and column determinant contributions on rectangular off-diagonal
blocks. No Haar-scaling theorem is assumed in constructing the character;
identifying this formula with Haar scaling remains a separate theorem.
No representation functors, geometric-lemma statement, or transitivity theorem
is claimed here.
