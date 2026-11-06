# Functoriality of the full derived subgroup

For actual group schemes over any scheme of universe `u`, every homomorphism
sends the full scheme-theoretic derived subgroup into the full derived
subgroup of the target, on every test scheme. The construction
`IsDerivedSubgroup.map` gives the induced homomorphism between any supplied
closed representatives. Its composite with the target inclusion equals the
source inclusion followed by the original homomorphism.

This is internal support for the arbitrary-field normal-complement construction.
It uses the existing definition of the derived subgroup as the intersection
of all closed subgroups containing every commutator. Pull back any closed
competitor in the target along the homomorphism. The pullback is closed,
and homomorphisms preserve commutators, so it is an admissible competitor
in the source. Minimality of the source derived subgroup proves the required
containment. Applying that containment to an isomorphism and its inverse
gives the characteristic-subgroup equality.

No field, smoothness, connectedness, affineness, representability-existence or
finite-type assumption is used. The induced-map construction only assumes
the two given closed derived-subgroup representatives. This contribution
does not itself construct a semisimple normal complement.
