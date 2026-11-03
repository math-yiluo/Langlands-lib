# Comparing the actual kernel with a represented subgroup

`KernelRepresentative.iso q i hk` constructs an isomorphism of actual group schemes
from `kernel q` to `U`. Its premises are a monomorphism `i : U → G` over the
same arbitrary scheme base and equality of the images of `kernelι q` and `i`
on every relative test scheme. It uses the published uniqueness of representatives
of a subgroup functor. `iso_hom_comp` says that the isomorphism commutes with
the inclusions into `G`; `overIso` forgets only the group structure.

The companion lemmas transfer smoothness, affineness, geometric connectedness,
and connectedness of the total space from `U` to the actual kernel. The first
three use the structural morphism identity in the category of schemes over the
base and invariance under isomorphisms. Connectedness uses the induced
homeomorphism. Over a field, `KernelRepresentative.isUnipotent` transfers the
existing coefficient-representation predicate along the group isomorphism.
These lemmas make no assertion from equality only on rational points.

`IsUnipotentRadical.geometricallyConnected_kernel` specializes the construction
to a represented ground-field radical in an affine group. Closedness makes its
inclusion a monomorphism and its structure morphism affine. Its given smoothness
then implies finite type. Its given connectedness and the published
`geometricallyConnected_of_connected` theorem supply geometric connectedness,
which the comparison transfers to the kernel. The quotient map need not be
surjective or smooth for this comparison.

This is an internal construction derived from the published represented-subgroup,
group-kernel, geometric-connectedness, and unipotence-transport interfaces.
It neither constructs a quotient nor asserts pseudo-reductivity.
