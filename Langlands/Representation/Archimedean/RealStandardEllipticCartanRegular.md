# Regular coordinates for the real standard Cartan numerator

`regularCoordinates` requires distinct logarithmic radii among complex slots,
distinct logarithmic absolute values among real slots, and nonzero sine in each
complex angle. A complex slot then gives two distinct nonreal conjugate
eigenvalues. Within each slot type the distinct radii rule out coincidences
between slots.

`realStandardEllipticCartanRegular` proves density, nonvanishing for positive
induced weights, and extension of numerator equality from these coordinates.
For any pair of slots with equal radii, varying the first radius alone leaves
only one forbidden value. For an angle, the forbidden values are the integer
multiples of π. The finite intersections give a dense set and the construction
permits any real sign tuple.

At zero logarithmic radii and with all real signs positive, choose a common
angle π divided by one plus the sum of the positive induced weights. Each
weight times that angle lies between zero and π. Each complex factor is thus
a nonzero exponential difference, and all the real factors are one. The
permutation sums repeat the same nonzero product, which remains nonzero in
ℂ. Continuity of the finite numerator and density give a nonzero value at
regular coordinates. The same two facts extend equality of numerators.

This internal result uses the explicit formula in
`RealStandardEllipticCartanNumerator`. It supplies the nonvanishing and density
steps used to compare maximal elliptic rank and recover numerator equality
from a regular Cartan character formula.
