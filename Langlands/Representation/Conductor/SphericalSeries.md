# The actual spherical Laurent series

This internal construction works over every nonarchimedean local field, with
independent universes for the field and representation space. Its inputs are
an actual smooth representation of `GL_(n+2)(F)`, a Whittaker functional, a
model vector, and the published Jacquet normalization of the quotient measure.

`degreeCorankOneModelCoefficient` integrates the actual degree-restricted
Laurent integrand. The finite-dimensionality of its actual value span is
supplied by `SphericalCompact`, rather than assumed. The coefficient is
homogeneous of its integral degree. Evaluating at any tuple of complex units
gives the actual scalar degree integral on the left-unipotent quotient.
Scalar integrability follows from the proved compact support, local constancy
and regularity of the normalized measure.

All coefficients below one common degree vanish: the corresponding integrand
is zero, so its integral lies in the zero submodule. Thus its coefficient
support is bounded below. `corankOneModelLaurentSeries` packages these
coefficients as a genuine Mathlib Laurent series, implemented as a Hahn
series on the integers. Its coefficient formula and homogeneity are proved.
`specializedCorankOneModelLaurentSeries` applies unit-tuple evaluation to every
coefficient, and its coefficient formula identifies each coefficient with the
actual scalar quotient integral.

This is an internal deduction from the existing support, integration and
homogeneity constructions. It implements the formal-series step of Jacquet
2012, printed page 520. It asserts no convergence, rational continuation,
upper bound on the degree support, essential identity or conductor conclusion.
