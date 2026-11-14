# Root coordinates for a supplied orthogonal-cover torus

This internal comparison starts with the supplied split pinning, central cover,
and rational standard-torus transport. Postcomposing the cover with the returned
inner automorphism gives a central isogeny whose torus square is the given one.
The restriction to the split maximal tori is an isogeny. The published actual
root-datum homomorphism supplies a bijection on roots and transports each actual
coroot by the torus map.

Choose an actual root datum of the standard orthogonal torus. For each source
root, its inverse under this bijection has standard signed-pair coordinates.
The published type-D coroot calculation identifies its coroot with the same
signed coordinate vector. Naturality of the actual character/cocharacter
pairing therefore makes the source pairing with a pulled-back character the
integer coordinate dot product. Every standard root pulls back to an actual
source root.

The construction works over the original field in every characteristic and
uses no classification of diagram automorphisms. The rank bound supplies the
three coordinates needed by the standard coroot calculation. This module does
not descend vector weights or construct representation eigenvectors.
