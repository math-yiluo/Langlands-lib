# Bounded adjoint images from full-center kernel homomorphisms

This internal helper transfers algebraic bounds from a homomorphism whose full
scheme kernel is the center to the actual adjoint quotient. It works over an
arbitrary valuative field at every universe and uses no topology.

For an actual adjoint quotient `q : G → A` and a homomorphism `f : G → P` to an
affine group locally of finite type, assume that the range functor of the actual
kernel of `f` equals the full center of `G`. For every subset `S` of `G(F)`, a
bound on `f(S)` then gives a bound on `q(S)`.

The geometric auxiliary first treats a map that kills the center and whose
kernel range is contained in the center. The adjoint quotient universal
property gives its descended map `A → P`. The quotient is fpqc: flatness and
surjectivity are part of the actual quotient interface, and quasi-compactness
follows from affineness. The published fpqc kernel criterion makes the
descended map monomorphic on every test scheme. The adjoint source is smooth,
connected and affine, so the published schematic-image criterion makes this
map a closed subgroup embedding.

The bounded-image result obtains center annihilation from the exact kernel
equality and applies that closed embedding. Closed immersions between affine
schemes reflect algebraic boundedness because every regular function on the
source lifts to the target. The image of `q(S)` under the descended embedding
is exactly `f(S)`, by the quotient factorization identity. This proves the
claimed transfer without any lifting of rational points along `q`.

The provenance is the internal composition of the actual adjoint quotient
universal property, `FpqcHomDescent.mono_of_kernel_range_le`,
`HomImage.isClosedSubgroup_of_mono`, and
`isAlgebraicallyBounded_of_closedImmersion`. This is a helper for the adjoint
normalizer-image input to KP 2.2.16; it does not itself prove that input or the
bounded-open-normalizer theorem.
