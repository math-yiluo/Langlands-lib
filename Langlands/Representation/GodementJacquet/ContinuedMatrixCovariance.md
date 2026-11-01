# Norm-one covariance of continued matrix pairings

This internal construction specializes `ContinuedMatrixPairing` to actual
matrix coefficients and proves the covariance needed for compact smoothing
transfer. Rational existence for each test and vector is supplied explicitly.
No smoothness, irreducibility or supercuspidality hypothesis is used to derive
that existence here. The provenance is the actual right invariance of group
Haar measure, the determinant weight, the published norm-one Fourier change
of variables, representation multiplication and continuation uniqueness.

For an arbitrary topological field and a right invariant Borel group measure,
`matrixIntegral_translate_of_norm_one` proves
`Z(R_g Φ, s, f) = Z(Φ, s, h ↦ f(h g⁻¹))` when `|det g| = 1`.
Here `R_g Φ(X) = Φ(X g)`. Right translation preserves the group integral and
the determinant weight at every complex exponent. The change of variables
holds for the totalized integral without a convergence premise. It is then
used only with the actual rational-value specifications, which retain
convergence on a right half-plane and denominator nonvanishing there.
`matrixRationalPairing_translate_of_norm_one` transfers this identity to the
unique rational functions for any linearly parametrized coefficient family
whose two coefficient functions have the indicated right-translation relation.

The remaining definitions use every canonical p-adic field, its normalized
absolute value, residue cardinality and shared normalized GL Haar measure.
The field and representation carrier have independent universes. For a fixed
algebraic functional `ℓ`, `matrixCoefficientRationalPairing` is the continued
bilinear pairing for `f_v(h) = ℓ(ρ(h)v)`. Its specification is the actual shifted
value relation at exponent `s + jpssShift n`. Its covariance is
`B(R_g Φ)v = B(Φ)(ρ(g⁻¹)v)` for determinant norm one.

`matrixFourierEquiv_translate_of_norm_one` identifies the full plus Fourier
transform of `R_g Φ` with the right translate of the Fourier transform by
`inverseTranspose g`. It follows by evaluating the published two-sided
norm-one Fourier integral formula with left matrix equal to one. The supplied
scalar character, Haar measure and self-duality witness determine the actual
full Fourier equivalence and its exact nested square product measure.

`iotaFourierMatrixCoefficientRationalPairing` composes that full Fourier
equivalence with the continued pairing of the literal functions
`h ↦ ℓ(ρ(inverseTranspose h)v)`. Its actual shifted value specification is at
the Fourier-transformed test, with the same `q^(-s)` rational variable.
It is defined before reflection in that rational variable. Right translation
of the original test produces an inverse-transpose right translate after
Fourier transform; coefficient precomposition by inverse transpose changes
this back to `ρ(g⁻¹)` on the vector. Consequently this pairing has the same
covariance as the original pairing. These equalities are in the rational
function field and make no claims about evaluation at poles.
