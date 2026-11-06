# Detecting a self-centralizing torus from its zero Lie weight

The file constructs the actual centralizer comparison isomorphism
`torusCentralizerFactorIsoOfZeroWeight`. Over a field, let `i : T → G`
be a closed commutative subgroup, and let `j : C → G` be a closed
representative of its existing all-test centralizer. Suppose `T` and
`C` are smooth affine and `C` is connected. If the differential of
`i` fills the existing zero adjoint weight space, the canonical factor
`torusCentralizerFactor i hrep : T → C` is an isomorphism. It is the
forward map of the constructed isomorphism, and composing it with
`j` recovers the specified `i`.

The tangent argument works over every commutative base ring.
Every actual Lie vector of `C` maps into the zero weight of `G`,
by the existing all-test centralizer-to-zero-weight comparison.
Surjectivity of `Lie.zeroWeightMap i` supplies a vector of `T`
with this same image. Injectivity of the differential of `j`
then proves surjectivity of the differential of the canonical
factor. Over a field, that factor is a closed immersion between
smooth affine groups, with connected target. The existing
`Lie.isIso_of_surjective_targetMapLinear` makes it an isomorphism.

Now let `G` itself be smooth connected affine over any field,
and let `T` be a closed split torus. Its whole-group centralizer
has a smooth closed representative by the published field
centralizer theorem, and that representative is connected by
`IsSplitTorus.connectedSpace_centralizer`. The construction
therefore proves the exact all-test equality
`torusCentralizer i = SubgroupFunctor.range i` when
`Lie.zeroWeightMap i` is surjective. Equality between the finite
dimension of the zero adjoint weight and the actual Lie dimension
of `T` is sufficient: the zero-weight map is already injective
because `i` is monomorphic, so finite-dimensional linear algebra
makes it surjective.

The last theorem also proves `IsMaximalTorus i` from that dimension
equality, using the published self-centralizer criterion.
No reductivity or algebraic-closedness hypothesis is used.
Affineness of `T` is an explicit typeclass in the interfaces and
follows from splitness in applications.

The provenance is internal: this composes existing actual
centralizer factorization, Lie-kernel maps, centralizer smoothness
and connectedness, tangent subgroup equality, and the all-test
self-centralizer maximality criterion. It supplies the field
criterion needed to apply relative zero-weight rank constancy.
This file does not itself construct a neighbourhood on which
those ranks agree, and does not prove openness of reductivity.
