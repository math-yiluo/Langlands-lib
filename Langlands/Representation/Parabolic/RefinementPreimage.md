# Actual preimages of subgroups of a block Levi

This is a derived construction supporting normalized refinement transitivity.
The algebraic part uses an arbitrary commutative ring `R`, a positive ordered
block shape `B` of total rank `n`, and an actual subgroup `H` of `B.Levi R`.
It requires no field, smooth representation, or admissibility hypothesis.
The topology part assumes a topological commutative ring, and the closedness
lemma additionally assumes that `R` is Hausdorff and `H` is closed.

## Construction

Let `G = GL_n(R)`, `P = B.parabolic R`, `M = B.Levi R`, and
`pi = B.leviProjection R`. The module imports the actual matrix constructions
from `Langlands.Group.GL.Blocks`.

`leviPreimage R B H` is the image in `G` of the subgroup `pi⁻¹(H)` of `P`.
Thus its elements are actual matrices; membership is exactly membership in
`P` together with membership of the diagonal-block projection in `H`.
`preimageInParabolic` is the inclusion into `P`.
`preimageProjection` maps such a matrix to its diagonal blocks, now valued
in the actual subgroup `H`. `preimageSection` sends an element of `H` to
its block diagonal matrix. Projection after section is the identity, and
projection is surjective.

`preimageProjection_ker` identifies the kernel with the original ambient
unipotent subgroup restricted to `leviPreimage`. `radicalInPreimage`
includes the original relative radical in the preimage.
`preimageUnipotentPart` is the original factor `g * section(pi(g))⁻¹`.
`preimageDecomposition` is the explicit equivalence

    leviPreimage R B H ≃ B.unipotentRadical R × H.

Its inverse multiplies the radical factor by the block diagonal factor.
This is an equivalence of sets, not an isomorphism with the direct-product
group. Both inverse laws are proved using the original split projection.

For a subgroup `K` of `H`, `preimage_subgroup` proves that taking its preimage
through `preimageProjection` and then its image in `G` gives precisely the
same subgroup as `leviPreimage R B (K.map H.subtype)`. All membership
identifications are proved; no chosen equivalence is a parameter.

`preimageProjectionContinuous` and `preimageSectionContinuous` bundle the
same homomorphisms with their continuity proofs. The factorization extends
to `preimageDecompositionHomeomorph` for the actual subgroup topologies.
Finally, `isClosed_leviPreimage` follows by continuous preimage inside `P`
and the closed inclusion of the original block parabolic into `G`.

## Provenance and scope

The source motivation is Bernstein--Zelevinsky, *Induced representations
of reductive p-adic groups I* (1977), Proposition 1.9(c), printed page 445
(PDF page 6), and sections 2.1--2.3, printed page 446 (PDF page 7).
The registered original is `bernstein-zelevinsky-1977-induced-i`,
SHA-256 `8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Those pages describe composition of parabolic triples, the standard
block-Levi specialization, and transitivity of normalized functors.

This module supplies elementary preimage constructions derived from the
already implemented split matrix projection. The extension to arbitrary
commutative rings and arbitrary subgroups `H` is justified by the
implemented algebraic proofs; it is not attributed to the source's
analytic theorem. Topological statements likewise use only the specified
topological-ring and closedness assumptions.

Taking `H = Geometric.refinedParabolic R B S` gives the direct smaller
ambient parabolic needed for a block refinement `S`; taking
`H = Geometric.refinedUnipotent R B S` gives its ambient radical candidate.
The module deliberately does not identify these with a chosen flattened
block shape, construct the inner refined Levi projection or its modulus,
or assert normalized induction or Jacquet transitivity. Those further
definitions and theorem obligations remain separate. No representation
functor, Haar-modulus identity, or theorem witness is assumed here.
