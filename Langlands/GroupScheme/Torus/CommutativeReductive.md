# Commutative reductive group schemes are relative tori

For an arbitrary base scheme, `commutativeReductiveMaximalTorusIso` constructs
an isomorphism from a commutative reductive group scheme to any specified
relative maximal torus in it. The isomorphism composed with the torus inclusion
is the identity of the ambient group. The torus inclusion is assumed closed,
and maximality means maximality on every residue-field fibre.

`relativeTorus_of_commutative_reductive` proves that every commutative reductive
group scheme is a relative torus, meaning that it becomes a finite split torus
on an étale cover. No condition on the base or constancy of the rank is imposed.

This is internal support derived from published results. Relative maximal-torus
self-centralization identifies the range of the torus inclusion with its full
all-test-scheme centralizer. Commutativity makes that centralizer the whole
ambient group. The inclusion and the identity therefore represent the same
subgroup functor, and uniqueness of representatives supplies the isomorphism
and its compatibility with the inclusion. Étale-local maximal-torus existence
provides a closed split maximal torus near each base point. These neighbourhoods
form a cover, on which the constructed isomorphism identifies the ambient group
with that split torus.

This support result does not assert the derived-group torus or parabolic
correspondence.
