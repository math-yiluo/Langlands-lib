# Holomorphic division from complex line slices

`exists_open_division_circle` starts with a scalar holomorphic denominator on an
open subset of a complex normed space. Its germ is nonzero at the center. The proof
chooses a nearby point where the denominator is nonzero and uses the direction from
the center to that point. The denominator restricted to this line has isolated zeros,
so a small circle about the center avoids them. Compactness of the translated
circle and continuity of the denominator give one open neighborhood of the center
throughout which the circle avoids the zeros. The corresponding disks stay in the
original open set.

`circleDivision` averages the quotient of the numerator by the denominator over
this circle in each parallel line. `differentiableOn_circleDivision` proves
holomorphy in the base point for finite-dimensional parameter spaces, using the
Library's holomorphy theorem for circle averages of translations.

`mul_circleDivision_eq` applies when the restricted denominator divides the
restricted numerator analytically in a neighborhood of each point of the slice
disk. The proof constructs a holomorphic quotient on the disk by taking the value
of a local quotient at each point. The local quotients agree near any point by
cancellation off the isolated zeros and by their prescribed value at the point.
The mean value property identifies the quotient at the center with the circle
average. After multiplication by the denominator this gives the numerator at the
center. The contour is independent of the numerator, so the construction gives one
common neighborhood for any family of scalar numerators.

This is a derived analytic step for passing from linewise pole detection to the
local pole bound in Bernstein–Lapid, *On the meromorphic continuation of Eisenstein
series*, §8.6. It uses the scalar Cauchy argument for translated circles in
`ImaginaryHyperplaneDivision` and the mean value theorem in Mathlib.
