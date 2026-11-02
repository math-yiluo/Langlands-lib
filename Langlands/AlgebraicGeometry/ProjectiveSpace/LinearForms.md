# Homogeneous linear polynomials and coordinate linear forms

This internal algebraic comparison uses the existing polynomial coordinate ring
and total-degree grading of `ProjectiveSpace R n`, for an arbitrary commutative
ring `R` and every natural `n`.

`degreeOneBasis` proves that the actual coordinate variables form a basis of
`projectiveSpaceGrading R n 1`. Its construction combines Mathlib's linear
independence of the variables with its equality between this submodule and
their span. The coercion formula identifies each basis element with `X j`.

`linearFormPolynomialEquiv` is an actual linear equivalence from linear
functionals on `Fin (n + 1) -> R` to the homogeneous degree-one submodule.
It first records a functional's values on the standard coordinate basis,
then uses these values as coefficients in the variable basis. The resulting
polynomial is exactly `sum j, ell (Pi.single j 1) * X j`.

`eval_linearFormPolynomialEquiv` proves that evaluating this polynomial at
a coordinate vector gives the original functional at that vector. The proof
uses the displayed sum formula and the standard basis expansion of the vector.
`linearFormPolynomialEquiv_coe_ne_zero` identifies nonzero functionals with
nonzero polynomials by injectivity of this linear equivalence.
`eval_eq_inverse_linearFormPolynomialEquiv` records evaluation in the reverse
direction for every actual homogeneous linear polynomial.

The provenance is internal linear algebra over the published polynomial
coordinate ring, using the cited Mathlib basis and grading constructions.
This comparison does not construct coordinates for scheme-valued points,
identify homogeneous-prime incidence with evaluation, prove a torsion bound,
or establish moduli representability. Those geometric comparisons remain
separate obligations.
