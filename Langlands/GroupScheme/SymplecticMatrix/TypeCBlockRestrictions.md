# Simple type C restrictions along a prescribed block torus

This internal adapter expresses actual character restriction along the
repeated-block torus in integer coordinates. Given a character whose
coordinates are a numbered simple root of type C, its image is the
`TypeCBlockWeights.simpleRestriction` vector. The proof writes the character
as a difference of coordinate characters or twice the final coordinate
character, then uses the explicit block-character identity.

The construction uses the supplied torus map and the Library's actual
character lattice. Its provenance is the existing block homomorphism,
coordinate root datum, and elementary additivity; it uses no classification
of forms or distinguished vertices as an input.
