# Disjoint sums of actual atlas nets

Author: Worker 56. Internal construction from the existing net and embedding
APIs. Work in the actual topological sigma space of a family of spaces, with
independent component and index universes. The component families may have
overlapping members and may contain empty members.

`sigmaFamily` is exactly the family of images of all component members under
the corresponding sigma injections. `IsQuasinet.sigmaFamily` sends a finite
witness family at a component point to its finite image family. Every image
member contains that point, and the union contains the image of the original
neighborhood union. The sigma injection is open, so this image is a neighborhood
in the sigma topology.

`IsQuasinet.restrictedFamily_image` first transports the restricted quasinet
along the actual subspace homeomorphism supplied by an embedding. The transported
family is contained in the family of ambient image members inside the image
subspace. Quasinet monotonicity gives the claimed restricted quasinet.

`IsNet.sigmaFamily` uses the preceding quasinet construction. Two members from
the same component have intersection equal to the image of their intersection,
because the sigma injection is injective. The component net supplies the
restricted quasinet, and the embedding lemma and monotonicity put it in the
sigma restricted family. Members from different components have empty
intersection: a point of both would force equality of their component tags.
The quasinet condition on that empty subspace is vacuous.

`IsCompactFamily.sigmaFamily` sends compact members along the continuous sigma
injections and transports their Hausdorff subspace structures along the actual
embedding homeomorphisms. No ambient Hausdorffness or local compactness is
required. These are internal topological constructions; they assume no output
net, analytic atlas, domain algebra, gluing or site structure.
