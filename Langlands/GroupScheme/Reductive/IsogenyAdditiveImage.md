# The actual image of a finite homomorphism from an additive line

This internal derived construction identifies the actual schematic image of a
finite homomorphism from a one-dimensional vector group to an affine group
locally of finite type over an arbitrary field with the standard additive line.
The source vector structure is given by natural coordinates on every scheme
test. The kernel can be nonreduced; no separability or perfectness is assumed.

The projection onto the schematic image is finite because its composite with
the closed image inclusion is the given finite morphism. Published image
geometry makes this projection flat and surjective and makes the image smooth
and connected. The published quotient theorem for the additive line says the
image is either trivial or another one-dimensional vector group. In the trivial
case its Lie algebra is zero. Flatness and local quasi-finiteness preserve the
Lie dimensions of smooth affine groups, whereas the source's vector coordinates
give dimension one. This contradiction eliminates the trivial case.
`additiveImageIso` chooses the actual isomorphism supplied by the resulting
vector-group predicate.

Provenance: derived from `HomImage`'s schematic-image geometry,
`RelativeRoot.trivial_or_isVectorGroup_of_flat_surjective`, the actual
vector-coordinate isomorphism, and
`Lie.finrank_kernel_eq_of_flat_locallyQuasiFinite`. This is an image-geometry
prerequisite for the general isogeny root comparison. It does not identify a
root, construct the root index equivalence, or prove the complete comparison.
