# Openness of the semisimple geometric identity-component locus

The theorem `identityComponentSemisimpleLocusOpen` has type
exactly the published `IdentityComponentSemisimpleLocusOpenStatement`
in every universe. It applies to every smooth affine group scheme over every
scheme and adds no hypotheses.

The proof combines the affine good-open theorem
`splitTorus.exists_open_subset_identityComponentSemisimpleLocus` with the
lifting/descent assembly in `IdentityComponentSemisimpleLocusLiftingReduction`
and the proved `relativeSplitTorusLifting`. The affine theorem recognizes
semisimplicity by the finiteness of the quotient of the fixed integral exponent
lattice by the span of the actual geometric roots. On a neighbourhood where
the identity components remain reductive, the given torus remains
self-centralizing and the complete root support is unchanged, that quotient
stays fixed. Its finite-root-index criterion therefore preserves semisimplicity,
including finiteness of the actual scheme-theoretic centre.

The assembly chooses a maximal torus after a finite Galois residue extension,
realizes the extension on an etale neighbourhood and lifts the split torus
on a further etale neighbourhood. The affine theorem constructs a good open
in an affine chart. Its image through the open chart and etale projections
is an open neighbourhood of the original point in the semisimple locus,
because that actual locus commutes with arbitrary base change. Pointwise good
opens prove openness by the usual topological neighbourhood criterion.

This is a derived proof using the Library's actual geometric fibres, identity
components, root supports, finite-root-index criterion, maximal-torus transport,
and relative torus lifting. It does not require a representable relative
centre or an a priori relative identity-component model.
