# Explicit witnesses of the polarized isogeny relation

A witness from one pointed representative to another is an equivariant
rational isomorphism with a rational unit multiplier. It must satisfy the
polarization equation `Multiple`, and its induced `levelIso` must send the
first representative's orbit to the second representative's orbit.

`witness_trans` composes two such witnesses with the product multiplier.
It obtains the polarization equation from `multiple_trans` and the
orbit equation from `levelIso_trans` and the two given orbit equations.
`witness_symm` uses `multiple_symm` and `levelIso_symm` for the inverse
isomorphism and reciprocal multiplier.
