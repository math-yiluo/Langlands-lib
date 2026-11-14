# Linear equivalences of polynomial vector groups

This internal construction realizes a linear equivalence between finite free
coordinate modules over any commutative ring as an actual group-scheme
isomorphism. The two coordinate index sets can have different stated sizes.
The forward and inverse rectangular matrices multiply to the respective identity
matrices, so the existing all-test matrix homomorphisms are inverse.

`linearIso` takes the matrices of a linear equivalence and its inverse in the
standard function bases. Its coordinate formula holds on every scheme over the
coefficient spectrum. On sections over the coefficient ring itself,
`sectionCoordinates_linearIso` gives exactly the original linear equivalence.
The proof removes the canonical spectrum/global-section identifications by
their inverse identities, then uses the standard matrix formula for a linear map.

This is derived linear algebra supporting the actual root-coordinate comparison
in `Rational/RootFieldVectorIso`; it adds no premise about root filtrations.
