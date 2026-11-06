# Compact quotient support from the mirabolic Kirillov support property

This internal derived unit isolates the support argument needed for row tests
vanishing at zero. `HasMirabolicCompactTranslates` means that every right
translate of an ambient function has compact support modulo the actual upper
unipotent group when restricted to the actual mirabolic subgroup. This is an
explicit support hypothesis, not an assertion of the supercuspidal Kirillov
theorem.

Given this property and a compact open subgroup fixing the function on the
right, a row Schwartz–Bruhat test vanishing at zero gives compact quotient
support. Its support is compact and avoids zero. Cover it by the open right
subgroup orbits of its nonzero rows and take a finite subcover. On each orbit,
an ambient matrix factors as a mirabolic matrix times a fixed representative
and an element of the fixing subgroup. The mirabolic support property for
that representative bounds its nonzero points modulo the upper unipotent
group. Multiplication by the representative and compact subgroup, projection
to the quotient, and finite union preserve compactness.

Consequently, for a standard Whittaker function with this property, any
inverse-character Whittaker function, and any such row test, the actual
equal-rank quotient integrand has compact support at every complex spectral
parameter. This conclusion uses pointwise support and requires no integrability
premise. Applying the result to supercuspidal coefficients requires the Kirillov
compact-support theorem; Laurent continuation is a subsequent step.
