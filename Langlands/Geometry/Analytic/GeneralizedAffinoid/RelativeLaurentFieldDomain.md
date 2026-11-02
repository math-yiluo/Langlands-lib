# Full domains over the independent Laurent coefficient field

This internal construction recasts the actual relative Laurent extension of a
full represented affinoid domain as a full represented domain over the independent
completed Gauss Laurent field. The two fields and all presentations remain in
universe `u`. The original field is complete and ultrametric, the Laurent radius
is positive, and no nonzero integer power of that radius is a scalar norm.

The auxiliary `ScalarRestriction.existsUnique_factor_over_extension` compares
the test classes. Suppose the extension field has an isometric actual affinoid
presentation over the original field. Every extension-field affinoid test then
has the original-field presentation and bounded equivalence constructed in
`AffinoidScalarRestriction`. A bounded map into that test can be conjugated into
its original-field presentation. The original full representation property
supplies a unique bounded factor. Conjugating it back preserves the bound. Its
compatibility with the structural map forces it to preserve the extension
scalars, because those scalars already come from the base algebra. Uniqueness
follows by the reverse conjugation. No strictness restriction on tests is used.

`transportOverExtension` retains the completed scalar action because actual
annulus transport commutes with `completedScalarMap`. `fieldMap` conjugates this
map through the actual bounded coefficient-presentation equivalences.
`fieldMap_spectrum` proves the corresponding spectrum square.

`fieldLocus` is the inverse image of the previously constructed lifted domain
locus under the actual spectrum homeomorphism. It is closed. The spectrum square
and surjectivity of both homeomorphisms identify it with the exact spectrum image
of `fieldMap`. To prove its universal property, compose a coefficient-field test
map with the ambient presentation equivalence, apply the test-class comparison
using the isometric Laurent-annulus field presentation, and compose the unique
factor with the inverse domain-algebra equivalence. The inverse identities
prove the structural equation and uniqueness. `fieldDomain` packages this full
representation with its actual algebra, map and locus.

All constructions are internal consequences of the existing scalar-restriction,
Laurent scalar-extension, bounded pushout and full-domain APIs. They retain
arbitrary positive original and test radii, arbitrary closed ideals, trivial
original valuations and zero or nonreduced quotients. They do not yet assert
strictification or the host finite rational-cover proposition.
