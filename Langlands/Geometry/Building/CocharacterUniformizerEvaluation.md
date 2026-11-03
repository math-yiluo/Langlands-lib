# Intrinsic uniformizer evaluation for the Jacquet adapter

This derived supporting module evaluates an actual character on an actual
cocharacter using the already published integer character–cocharacter pairing.
It chooses no split coordinates and needs no splitness hypothesis for that
identity. The composition is an endomorphism of the multiplicative group;
`gmEndEquiv_symm_comp` identifies it with the integer power prescribed by
`latticePairing`.

For the chosen order-one uniformizer, the rational-character valuation of the
intrinsic lattice section is the integer pairing. The residue-normalized norm
is the residue cardinality raised to the negative pairing. A positive pairing
therefore has norm less than one. These are only evaluation identities: no
injectivity, representative uniqueness, or full split-torus section theorem is
asserted here.

This implements the sign step needed by the actual simultaneous-basis Jacquet
adapter. Its provenance is internal derivation from `CocharacterUniformizer`,
the intrinsic torus lattice pairing, and the published local-field norm and
order laws; it uses no additional literature assertion.
