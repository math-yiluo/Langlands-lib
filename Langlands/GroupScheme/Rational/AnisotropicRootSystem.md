# The actual relative root system for anisotropic groups

This module proves the empty case needed by `RelativeRootSystemStatement`.
It uses the actual character lattice, rational relative-root span and normalizer
modulo centralizer quotient imported from `Rational.Statement`. It assumes no
root-system or faithfulness premise for anisotropic groups.

`RelativeRootSystem.emptyPairing` is the internal empty-index construction on a
subsingleton rational vector space. Its bilinear map is exactly evaluation on
the dual. Both maps to the respective duals are bijective because the spaces are
subsingletons. The empty root and coroot embeddings span their zero ambient
spaces; all reflection and crystallographic laws have empty quantifiers.

`hasRelativeRootSystem_of_empty` constructs all clauses of the published
`HasRelativeRootSystem` when the actual relative roots are empty and the actual
relative Weyl quotient is a subsingleton. The rational root span is zero, both
Weyl images are the unique subgroup of its automorphism group, and the quotient
action is injective because its domain is a subsingleton. This intermediate
lemma explicitly retains those two hypotheses.

The anisotropic application discharges both hypotheses without reductivity or
maximality assumptions. The published split-rank argument gives at most one
homomorphism from any split subtorus to any group scheme. Thus every rational
point centralizes it and its normalizer modulo centralizer quotient is trivial.
The published `IsAnisotropic.relativeRoots_eq_empty` supplies the empty root set.
`IsAnisotropic.hasRelativeRootSystem` therefore proves the actual root-system
assertion for every split subtorus in an anisotropic affine group.

These are derived internal results, by direct unfolding of the existing
constructions and the published anisotropy lemmas. They address the anisotropic
case of the general relative-root theorem described in the paired
`Rational.Statement.md`. They do not prove its isotropic case or supply any
rank-one reflection or generation theorem.
