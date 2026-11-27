# Transport of cleared unitary bounds for rational operators

These lemmas give the vectorwise norm estimates used to pass from the
bounded dense unitary values in Waldspurger V.2.3, printed p. 294, to a
bound for any cleared presentation and to change the compact carriers.
The estimates are derived from `HasClearedUnitaryBound` and the existing
polynomial and rational continuation interfaces.

`exists_normedComplexModel` supplies a normed model in the same universe
for an algebraic output space, by the ℓ² norm of finitely supported basis
coordinates.

`hasClearedUnitaryBound_postcomp` restricts a fixed linear map to the
finite-dimensional value span of the numerator applied to one vector.
`IsPolynomialOn.finiteDimensional_valueSpan` supplies the dimension
property. The continuous linear map on that span bounds the new
numerator by its operator norm times the old bound.

`hasClearedUnitaryBound_precomp` expands a varying polynomial linear map
at each input as a finite sum of fixed vectors with regular coefficients.
The coefficients are bounded because the unitary parameter group is
compact. Summing the bounds for the fixed vectors gives the result.

`hasClearedUnitaryBound_of_cross` cancels the nonzero denominator on its
dense unitary nonvanishing set and invokes
`hasClearedUnitaryBound_of_dense` for the new numerator and denominator.
`hasClearedUnitaryBound_of_crossOn_open` first extends a cross identity
from a nonempty ambient open set using
`rationalUnramifiedPolynomial_eq_zero_of_isOpen` on each input vector.

The source of the dense-unitary bound argument is
`waldspurger-2003-plancherel`, SHA-256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`,
Corollary V.2.3, printed p. 294.

`hasClearedUnitaryBound_restrict` and `polynomialOperatorOn_restrict_univ`
restrict the parameter along a map of affine group schemes. Norm-one
characters restrict to norm-one characters, and each regular coefficient
restricts along the same morphism.
