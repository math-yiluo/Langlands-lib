# Weyl-normalized root families over arbitrary local rings

This internal construction combines the published arbitrary-local-ring
theorems `LocalRootGroup.exists_rootParametrization_of_flat` and
`LocalSplitCell.exists_unit_weylNormalization`. Its family assembly adapts
the proof of `localSplitSimpleRootGroup` in
`LocalSplitReducedIsomorphismProof`, using the stronger published inputs
instead of the reduced-ring parametrization and normalization results.

Let `R` be any commutative local ring and `G` a reductive group scheme over
`Spec R` with affine structure morphism. Supply a closed coordinate split
torus inclusion that is maximal on every residue-field fibre, a fibrewise
coordinate root datum `P`, and a base `b` of that datum. No reducedness,
noetherian, henselian or characteristic hypothesis is imposed.

`exists_normalizedLocalRootFamily` first chooses an actual parametrization
for each root. For every simple root `a`, the published unit normalization
rescales its chosen negative-root parametrization by a unit so that
`u_{-a}(-1) u_a(1) u_{-a}(-1)` acts on the torus by the root reflection.
Unit scaling preserves the root-parametrization predicate.

The final family replaces only the negative-simple entries. A negative
simple root is not simple, so all chosen positive-simple entries stay
unchanged. Distinct simple roots have distinct negatives, by injectivity
of the root map. These facts make all replacements consistent. At a
replaced entry, the new map is the normalized parametrization of precisely
that root; elsewhere the original parametrization remains. Thus the result
parametrizes every root and has the required Weyl point at every simple
root.

`normalizedLocalRootFamily` chooses such a family. Its two specification
theorems record all-root parametrization and the simple Weyl-point
identities. The published `localSplitSimpleRootGroupLocal` theorem is
imported from `LocalSplitSimpleRootGroupLocal`; its simple-root conclusion
remains available without a duplicate declaration. The all-root family
and its chosen parametrizations in this module are retained separately.

The construction is over local rings. It does not assert simultaneous
normalization over an arbitrary nonlocal coefficient ring, prove any
rank-one Bruhat relation, or give the negative-simple cell translation law.
