# The unique possible rank-one marking in actual type G2

This internal module works over any field in arbitrary universe `u`.
It uses an actual `TitsIndexData G` of an affine locally finite type
group scheme and a supplied equivalence identifying every actual Cartan
entry with Mathlib's `CartanMatrix.G₂`. It requires neither a local-field
hypothesis nor simple connectedness nor an anisotropic-component premise.

`TitsIndexData.starIsTrivial_of_type_G2` combines matrix rigidity with
the published Cartan-preserving property of the full absolute Galois
star action. Every full Galois element fixes both actual simple vertices.

`TitsIndexData.G2_rankOne_marking` assumes `splitRank G = 1`. It concludes
the exact `IsNumberingOf` predicate with distinguished subset
`i.val = 0`, together with triviality of the full star action.
In Mathlib's root-on-coroot pairing convention, vertex zero is the long
root: its pairing with the coroot of vertex one is minus three.

The implemented proof uses the published rank-one orbit theorem and
triviality of the star action to obtain a singleton distinguished set.
If its vertex were vertex one, vertex zero would have zero restriction.
Reflecting the actual root at vertex zero in the root at vertex one
produces an actual absolute root whose restriction is three times the
distinguished restriction. The published
`rootRestriction_ne_nsmul_of_three_le` forbids this, including for
possibly nonreduced relative root systems. Thus the distinguished
vertex is zero, and injectivity of the numbering gives both directions
of the exact marked-set comparison.

The provenance is internal composition of actual-index orbit and
root-restriction theorems with the explicit G2 matrix and one root
reflection. No new literature claim is introduced. All characteristics
are retained. This result does not exclude the remaining long-root
marking or prove the local G2 exclusion or
`LocalRankOneTitsIndexStatement`.
