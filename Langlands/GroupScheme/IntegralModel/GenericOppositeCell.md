# Generic opposite-cell coordinates of integral sections

Worker 248. Internal supporting results at arbitrary universe `u`.

For an affine group over a field, a homomorphism from a commutative group
scheme and a cocharacter of that group scheme, assume explicitly that the
dynamic centralizer of the composite cocharacter equals the centralizer of
the entire source. A rational point normalizing the source and expressible as
a product in the opposite-unipotent and parabolic subgroups then centralizes
that source. The proof decomposes the parabolic factor as a unipotent factor
times a Levi factor using `RationalPoint.existsUnique_unipotent_mul_levi`.
The centralizer equality makes the Levi factor centralize the source.
Removing it leaves a normalizing product of opposite unipotent points, which
is the identity by `normalizer_eq_one_of_unipotent_product`.
No genericity or maximality hypothesis is suppressed: their relevant
consequence is the explicit centralizer equality.

For a supplied integral model over a domain with its specified fraction
field, a cocharacter of the model, and supplied representatives of its
opposite-unipotent and parabolic functors, an actual integral opposite-cell
coordinate gives corresponding generic opposite-cell factors of the same
point. The proof applies `baseChangeSectionHom` to each coordinate,
uses base-change compatibility of the represented dynamic subgroups,
and transports both points through the model's specified generic
identification. Naturality and the homomorphism law show that their product
is precisely `integralPointMap` of the original section. There are no
smoothness, Henselian, residue-field, or quotient-surjectivity assumptions
in this coordinate lemma.

`IntegralModel.genericOppositeCellFactorPair` selects such a pair, retaining
its opposite-unipotent membership, parabolic membership, and exact product
equality in a subtype. It uses classical choice from the preceding
coordinate lemma with the same integral model, cocharacter, representatives,
representation proofs and actual integral coordinate.

These are internal consequences of the imported Library decomposition,
separation, base-change and actual integral-point APIs. They do not assert
an integral root-depth criterion or the final unramified facet root datum.
