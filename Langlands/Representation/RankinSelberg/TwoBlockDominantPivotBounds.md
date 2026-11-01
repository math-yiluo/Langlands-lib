# Opposing Iwasawa bounds about the dominant singleton

This is derived internal support infrastructure for the actual strict-dominant
matrix in JPSS (1983), Section 4.10(2), printed page 419, registered source
`jpss-1983-rankin-selberg`. It combines the isolated singleton proved in
`TwoBlockDominantPivot` with the published integer simple-root support theorem
for smooth coefficient-image vectors. It asserts support in the Iwasawa
coordinates of the actual matrix; rectangle-volume estimates and convergence
are separate obligations.

`PivotCone L i lam` packages adjacent integer root bounds with constant `L`,
the normalization `lam i = 0`, and the resulting opposing cone with bound `r*L`.
The coefficient and actual-matrix theorems produce this same predicate.

`oppositeCone_of_pivot` propagates adjacent root bounds from a zero exponent
at a specified pivot. Coordinates before the pivot are bounded below by
`-r*L`, and coordinates after it are bounded above by `r*L`. The proof uses
the existing interval propagation lemma for `RootBounded`.

`torusExponent_pivot` applies the isolated-unit absolute-value theorem to a
canonical Iwasawa decomposition. The normalized absolute value of a uniformizer
power is the residue cardinality to the negative exponent. Since that
cardinality exceeds one, absolute value one forces exponent zero.

`exists_coefficient_pivot_cone` chooses one integer root bound for a supplied
smooth coefficient-image vector, before every matrix, pivot and decomposition.
Upper-unipotent equivariance transports nonvanishing to the diagonal times
integral factor, where the existing smooth simple-root theorem applies.
The pivot fixes its exponent, and interval propagation gives the cone.
`exists_matrix_pivot_cone` supplies a canonical Iwasawa decomposition and applies
this result to the actual dominant matrix for every group representative,
both rectangles and complementary sizes, including zero dimensions.

Only smoothness is required of the supplied representation. There is no
irreducibility, nonzero-functional or integrability assumption. For a zero
coefficient the nonvanishing implications remain valid.
