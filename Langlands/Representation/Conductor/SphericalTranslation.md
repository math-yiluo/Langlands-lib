# Central translation of actual model coefficients

This internal unit derives change of variables under the actual coefficient
model action of `diag(ϖᵗ, …, ϖᵗ, 1)`. The scalar determinant weight is
multiplicative because both determinant norms are positive real numbers.

The spherical central shift formula gives the transformation factor:
the inverse determinant weight at the scalar torus matrix, multiplied by
the symmetric coordinate-product unit to power `-t`. The degree on the
quotient shifts by `(n + 1)t`. These identities follow from the actual
model action, the spherical formula and quotient representatives.

For a smooth representation over an arbitrary nonarchimedean local field,
`degreeCorankOneModelCoefficient_centralTranslate` proves the actual integrated
identity. If `Aₜ` denotes the factor above, `wₜ` is the translated vector and
`c(w,d)` is the degree coefficient, then

`c(wₜ,d) = Aₜ c(w,d + (n + 1)t)`.

The proof evaluates at every tuple of nonzero complex coordinates. The existing
coefficient evaluation theorem identifies each evaluation with its scalar
integral. The pointwise degree identity moves the factor outside that integral,
and right invariance in `IsJacquetNormalization` removes the quotient
translation. Evaluations separate symmetric Laurent polynomials, giving the
stated equality. Integrability and finite value spans already follow from the
smooth-model coefficient construction; they are not extra premises.

These are internal deductions from the actual model action, the previously
constructed central spherical formula, and the Jacquet-normalized measure.
The model is on `GL_(n+2)` and the integral is over `N_(n+1) \ GL_(n+1)`.
The field and representation space have independent universes.

No functional equation, L-polynomial existence, universal finite support,
essential identity or conductor conclusion is assumed or proved here.
