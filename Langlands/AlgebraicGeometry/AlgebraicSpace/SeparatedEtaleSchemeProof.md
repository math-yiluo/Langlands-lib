# Schemes from separated algebraic spaces with structurally etale atlases

The theorem `separatedEtaleScheme` proves the unchanged proposition
`SeparatedEtaleSchemeStatement` in every universe. The base scheme and the
algebraic space are arbitrary. There is no affineness, quasi-compactness,
Noetherian or finite-type assumption beyond the stated etale structural atlas.

Choose the supplied surjective etale atlas and use the terminal scheme over
the original base as the scheme target. The atlas composite to this target is
its etale structure map, and terminal uniqueness gives compatibility with the
sheaf map. The separated atlas-chart gluing theorem now gives an actual scheme
representative over the original base.

That theorem constructs affine source and target neighborhoods, represents
their local images by induction on affine etale field-fibre bounds and compact
quasi-affine descent, then glues the resulting open scheme charts. It uses the
closed diagonal and actual etale structural atlas; it never assumes that the
space is a scheme. The present wrapper simply applies that implemented result.
