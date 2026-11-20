# Recovering a lower unitriangular matrix from its compact factor

Multiplying a lower unitriangular matrix on the right by the long Weyl
representative puts it in the longest Bruhat cell. Its compact factor gives
the same left upper triangular coset. `lowerUnitaryCoordinate` recovers the
original lower matrix from the inverse of the published longest-cell
coordinate homeomorphism and conjugation by the long representative. It is
continuous on the unitary matrices in this chart. For an upper triangular
unitary matrix the recovered coordinate is the identity.

`exists_bound_of_lowerUnitaryCoordinate` starts with a continuous function
on the unitary group bounded above by one and attaining one only on upper
triangular matrices. The inverse image of a neighborhood of the identity by
the recovery map is relatively open in the chart. An ambient open set inducing
it contains every maximizer. Compactness gives a bound below one on the
complement, and hence on the compact factors of lower unitriangular matrices
outside the prescribed neighborhood.

This is an internal application of `UpperBruhatCoordinates.cellHomeomorph`
and `ComplexPrincipalSeriesExtension.phaseOrthPart_iwasawa`. The application
to continuous sections on the compact quotient of the induced representation
uses the setting of Wallach, *Real Reductive Groups I* (1988), Lemma 5.3.1,
printed pp. 144–145 (PDF pp. 164–165 of
`wallach-1988-real-reductive-groups-i`).
