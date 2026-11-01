# Common convergence and rationality for supercuspidal matrix coefficients

This internal consequence combines the compact scalar-support bridge with the
central matrix recurrence. It applies to an actual irreducible supercuspidal
representation over every canonical p-adic field, at every positive rank
`n + 1`. The field and representation carrier retain independent universes.
No analytic premise is added to supercuspidality and irreducibility.

`matrixUniformizer F n` is the scalar matrix of the specified field uniformizer,
regarded as an element of the full group center. Its determinant has normalized
absolute value `q^(-(n+1)) < 1`. The actual central character from admissible
Schur supplies its nonzero complex scalar `ω`. Every function in the entire
bi-smooth coefficient span has covariance under this same scalar matrix.

Inverse transpose sends a scalar matrix to its inverse. It therefore transports
the compact scalar cover to the image of its compact representative set, and
the transformed coefficient has scalar `ω⁻¹`. Continuity is preserved by the
actual inverse-transpose homeomorphism. This argument acts directly on the
functions in the original coefficient family; it needs no identification with
contragredient coefficients.

`SupercuspidalMatrixRationalityData` records common right half-planes for the
original and inverse-transpose families, and actual shifted rational
continuations for every full-matrix test and every coefficient in each family.
The shifts are the published `jpssShift n`, the spectral variable is `q^(-s)`,
and the Haar measure is the canonical normalized GL measure. Each continuation
includes its reduced-denominator guard. Each also has a Laurent numerator
after multiplication by the single geometric Laurent denominator attached to
the fixed scalar matrix and its family's scalar, respectively `ω` and `ω⁻¹`.
These two denominators are independent of the test and coefficient.

`exists_supercuspidalMatrixRationalityData` proves the data from supercuspidality
and irreducibility. The contracting determinant gives a common threshold for
each central scalar before the test and coefficient are chosen. The compact
scalar support and covariance then instantiate the existing geometric quotient
and rational-continuation theorems for every pair.

The provenance is the direct combination of imported support, Schur, scalar
matrix, recurrence and rational-evaluation results. This pair proves no
functional equation, denominator cancellation, Laurent-span equality, or
polynomial-one assertion.
