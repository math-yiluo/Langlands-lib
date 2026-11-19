# Finite series from the actual descended face quotients

This unit reduces the arbitrary-universe
`RelativeUnipotentRadicalFiltrationStatement` to the vector-bundle
identification of the actual globally constructed quotients.

For a supplied finite face-chart cover `D`,
`hasVectorBundleSeries_of_vectorBundleQuotients` applies the finite-segment
construction to the actual global face terms and their actual closed successive
maps. Smoothness of each next term, normality, the full represented fppf quotient,
the common finite termination bound, and all-test terminal triviality are already
proved. The quotient maps and groups are the prescribed
`globalFaceQuotientData`, rather than freely chosen replacement quotients.
Transport along `globalTermZeroIso` gives the series for the originally supplied
radical. The length is `D.bound`. This includes disconnected and empty bases and
does not require a common local bundle rank.

`relativeUnipotentRadicalFiltration_of_globalFaceQuotients` extracts the actual
finite cover over an affine base and proves the unchanged target once the
vector-bundle predicate is supplied for each actual global quotient. The
proposition retains its original universal quantifiers and assumptions.

This is an internal derivation using the constructed filtration, quotient descent,
and finite-segment interfaces. `CoordinateTorusRootTransport` uses the published
`RelativeRoot.subgroup_comap_of_transport` to match the original root ranges.
`SplitFaceRootRangeTransport`, `SplitFaceEtaleComparison` and
`FaceChartOverlapComparison` then give equality of weighted term ranges on
arbitrary overlaps. `FaceCoverTermDescent` constructs the actual global terms,
and `FaceCoverQuotientDescent` constructs the full fppf quotients used here.
