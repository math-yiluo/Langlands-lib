# Supporting functionals for finite conic combinations

This internal derived construction supplies a supporting functional for a finite
family of vectors over the real numbers. If a vector has a nonnegative coefficient
expansion and has no expansion with every coefficient positive, the constructed
linear functional is zero on that vector, nonnegative on every generator, and
strictly positive on at least one generator. No independence, distinctness,
nonzero-generator or ambient finite-dimensionality assumption is imposed.

The proof passes to the finite-dimensional image of the coefficient map and uses
finite coordinates there. The image of the strictly positive coefficient orthant
is open because the coefficient map onto its image is surjective. This image is
convex, so Mathlib's geometric Hahn–Banach point/open-set separation theorem
provides a separating functional. Arbitrarily large positive coefficients force
its values on generators to be nonnegative. The original nonnegative expansion
then gives nonnegativity at the given vector; scaling the all-ones expansion
toward zero gives the opposite inequality. Strict separation of the all-ones
expansion forces positivity at some generator. Finally, the functional on the
image is extended linearly to the original vector space.

`supportingFunctional` chooses the actual linear map, and its specification gives
the three properties. This is finite-dimensional linear algebra support for the
boundary-face step in the proof of Renard VII.2.4. It does not assert a parabolic
realization or a cocharacter existence theorem.
