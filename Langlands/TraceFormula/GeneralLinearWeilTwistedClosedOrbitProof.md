# Closedness of the rational twisted orbit in Weil coordinates

`generalLinearWeilTwistedClosedOrbit` proves
`GeneralLinearWeilTwistedClosedOrbitStatement`. The rational cyclic norm has an elliptic
associate over the base field. Irreducibility of its characteristic polynomial gives
positive rank, so the determinant-norm-one conjugators have the same orbit as all adelic
matrix conjugators by `isClosed_range_adelic_normOne_twistedConj`.

The comparison `generalLinearWeilNormOneHomeomorph` identifies the actual Weil norm-one
points with determinant-norm-one matrix units. `generalLinearWeilNormOne_twistedConj`
checks the compatibility of twisted conjugation using the adelic automorphism comparison
in `generalLinearWeilAdelicTwist`. The actual orbit is the preimage of the closed adelic
matrix orbit along the continuous coordinate map. This supplies the closedness condition in
Getz and Hahn (2024), Theorem 18.2.5, p. 479, and §18.5, pp. 487–488.
