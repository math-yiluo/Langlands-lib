# Ordinary classes and actual transport of full Tate-normalized CM models

Author: Worker 344.

This internal construction fixes a level whose Hodge image preserves the
original Harris integral source span. It quotients the existing full
`TateNormalizedCMRepresentative` values by
`TateNormalizedCMOrdinaryRelated`: an actual abelian-scheme isomorphism,
exact equivariance for the supplied integral order actions, integral
polarization cross-multiple data at the original rational scalar, and the
original level equation for the induced rational action isomorphism. The
geometric point fields are algebraically closed by the definition of
`HarrisGeometricPoint`.

The existing characterization of this relation by equality of original CM
classes proves reflexivity, symmetry and transitivity. The resulting quotient
is `TateNormalizedCMOrdinaryIsoClass`. Its class equality criterion is exactly
the ordinary relation. `tateNormalizedCMOrdinaryClassEquiv` compares it to the
unchanged normalized rational-isogeny quotient by the identity on actual
models in both directions. The existing relation equivalence makes both maps
well defined, and quotient induction proves the inverse identities.
`tateNormalizedCMOrdinaryForget` returns the same original CM class. Its
injectivity follows from that of normalized forgetting and the identity-on-models
equivalence. These constructions require neither existence of normalized
models nor lattice realization.

The point map is the quotient of the existing actual normalized
representative point map. Ordinary relatedness is preserved by first using the
unchanged normalized relation and then recovering the ordinary relation at
the destination. Quotient induction proves that its square with the identity
comparison of quotients commutes. Injectivity of that comparison transfers the
inverse, path independence, identity and composition laws from the existing
normalized point maps. Both arrows of the point equivalence use actual point
transport along the original path or its inverse.

Base change similarly descends the existing actual normalized representative
pullback, retaining its actual pulled-back abelian scheme, polarization,
integral order action, CM condition and original pulled-back level orbit.
The unchanged normalized relation is preserved by that pullback; the relation
equivalence recovers ordinary relatedness on the destination models. Quotient
induction proves the base-change square with the unchanged normalized
quotient. No inverse to a forgetful comparison defines either transport map.

The provenance is internal: all proofs use the existing ordinary-relation
comparison and actual normalized representative transport. No new external
assertion is assumed. This compares quotients of the same normalized models,
with source-stabilizer containment retained throughout. It does not construct
an independent ordinary PEL parameter scheme or prove representability.
