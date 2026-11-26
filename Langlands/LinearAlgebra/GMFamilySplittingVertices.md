# Affine vertices and the parabolic sections

`splittingIntercepts` uses the bounds for the two chambers translated by
opposite displacements. The Riesz vector `splittingVertex` represents a
functional at a basis intersection. Its translates by `ξ` and `−ξ` lie in the
Levi flats cut out by the chosen normals, and their difference is `2 • ξ`.
The uniqueness result for complementary flats identifies their positive root
sets with `splittingSection`.

Under `RegularDisplacement` every inequality outside the basis has nonzero
slack at that intersection. A simple root outside the chosen basis of a normal space
has nonzero restriction to the corresponding flat by independence. The
regularity of the translated point then makes its evaluation nonzero. These
signs give the equivalence between feasibility of the intersection and
incidence of both sections to their chambers. The two flats determine the
section points and thus the basis. Conversely, an incident pair of sections
with nonzero determinant determines the basis by taking precisely the
vanishing simple normals at its two points.
