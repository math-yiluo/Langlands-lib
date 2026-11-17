# Homogeneous quotients from affine local models

This derived construction globalizes actual homogeneous quotients of a smooth
monomorphic subgroup in a smooth affine group over an arbitrary scheme. Its
input supplies a quasi-affine homogeneous quotient after restriction to each
affine scheme mapping by an open immersion to the base. Its output is an actual
smooth homogeneous quotient, quasi-affine above every affine base open.

On the canonical affine open cover, each supplied quotient represents the same
restricted canonical fppf coset sheaf by `representableBy_baseChange`. The
published `LocalRepresentation.exists_representation` glues these full sheaf
representations to a scheme. Separatedness is local on the base and follows from
the supplied homogeneous quotients by
`LocalRepresentation.property_of_local_representations`.
`quotientOfIso` recovers the complete quotient structure and all-test coset
fibers on the global representing scheme; the quotient is smooth over the base
by smoothness descent from the ambient group.

For any affine base open, the global representative restricted there and the
supplied local quotient represent the same sheaf. Full faithfulness of the
lifted Yoneda functor gives their scheme isomorphism. Quasi-affineness transfers
through this isomorphism and through the canonical isomorphism between the
restricted scheme and the base-change pullback. The final definition chooses
the quotient with these proved properties. All content is derived from the
imported scheme gluing, representation and quotient constructions.
