# Frobenius point descent and subgroup transport

These internal derived helpers support the finite-field Borel-pair
proof of Milne's Proposition 17.99. They compose the published affine coordinate,
finite-field Frobenius, and canonical Galois descent interfaces.

The exact point descent helper uses global-section coordinates on an affine group:
Frobenius-fixed values lie in the original finite field, by the published
`FiniteFieldTorsorPoint.mem_range_algebraMap_of_pow_card_eq`. Descending every
coordinate gives an algebra map and therefore the prescribed original-field point
with exact pullback recovery.

The imported `GaloisPointComparison.rationalConjugate_naturality` proves that coefficient conjugation commutes with a
ground-field homomorphism. `galoisTransport_conjugate_range` identifies Galois
transport of a conjugated ground-field subgroup range with conjugation by the
transported point. `galoisTransport_range` proves Galois invariance of a
ground-field subgroup range. Both range statements hold on all test schemes.
