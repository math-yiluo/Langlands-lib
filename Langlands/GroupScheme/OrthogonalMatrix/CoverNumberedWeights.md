# Descended numbered vector weights of an aligned orthogonal cover

This internal construction uses the supplied pinning, central isogeny and full
scheme-kernel alignment. Simple connectedness gives the full integral coroot
span. The integer numbered-weight construction then supplies the vector weights
and their simple-root chain and fork identities on the actual source lattice.
Alignment applies to the vertex-zero weight because its simple-coroot values
are exactly the corresponding fundamental-weight values. Full fpqc character
descent through the supplied torus comparison therefore descends this weight.
Successive simple-root differences descend all remaining vector weights.

Character pullback is injective for the fpqc comparison. Consequently the
simple-root identities descend to standard coordinates. The actual coroot
comparison makes each prescribed simple-coroot pairing a coordinate dot
product. The integer Gram calculation forces orthonormality, so the descended
weights are a signed coordinate permutation. The structure stores that
permutation, its signs, the actual character factorizations and the numbered
simple-root identities. Every field characteristic and rank at least four is
retained. The construction does not assert an eigenbasis.

The signed index equivalence identifies an integer-unit sign with the positive or
negative standard weight. The stored coordinate equality therefore identifies
each descended character with the corresponding signed standard character.
Distinct numbered indices have distinct coordinate positions, so every choice
of two signs gives a standard type-D root. Pulling this root back through the
actual root comparison proves that every signed pair of distinct numbered
weights is an actual source root.
