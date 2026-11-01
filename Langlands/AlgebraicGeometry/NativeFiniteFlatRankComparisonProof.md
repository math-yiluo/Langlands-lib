# Native rank from affine sections and fraction fields

`nativeFiniteFlatRankComparison` proves
`NativeFiniteFlatRankComparisonStatement`.

For the first assertion, finiteness over the affine target makes the source
affine. The canonical `isoSpec` isomorphisms identify the map with the spectrum
of its actual map on global sections. Their naturality square is a pullback,
so the native rank agrees with the rank of that spectrum map. Mathlib identifies
it with the rank at a stalk of the global sections algebra, and then with the
dimension of its residue-field fibre. Since the target sections form a domain
and the module is finite and flat, that fibre dimension is the module finrank
over the domain.

For the second assertion the same spectrum-map and fibre comparisons give
`Module.finrank R S`. The canonical extension of the given algebra map to
fraction fields has the required scalar tower. Mathlib's
`IsFractionRing.finrank_eq` identifies the module finrank with the dimension
of the resulting fraction-field extension.
