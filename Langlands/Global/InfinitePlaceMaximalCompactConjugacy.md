# Conjugacy of archimedean maximal compact subgroups

`InfinitePlaceMaximalCompactConjugacyStatement` compares any two maximal compact
subgroups in the actual completion-point group of a connected reductive group
over a number field. It finds a point of that group whose conjugation sends the
first subgroup onto the second.

Pass to the connected reductive group over the completion using the given
multiplicative homeomorphism. The closed self-adjoint realization over that
completion supplies polynomial equations for its image. The compact-conjugacy
argument conjugates each compact subgroup into the unitary inverse image
using a point of the group. This inverse image is compact, so maximality of the
two conjugated subgroups makes both equal to it. The completion comparison
transports the resulting conjugation to the original point group.

This is an internal structural input for changing the reference compact in
the Eisenstein functional equation.
