# Positive-torus averaging of a finite-place tensor

`FinitePlacePositiveTensorStatement` concerns an affine group scheme
locally of finite type over a number field and a fixed finite place.
The morphism from the supplied split torus is central and the
restriction of rational characters along it is injective with
finite-index image. These choices define
`normOneFinitePlaceDecomposition` and `normalizedPositiveHaarMeasure`.

Take a complex-valued local function and a complex-valued adelic
exterior function invariant under right multiplication by the
insertion of the finite-place group. In the product coordinates of
the norm-one group, the positive average of their tensor is the
original local function times the positive average of the adelic
exterior function evaluated at the norm-one kernel point. The
averages use the normalized positive Haar measure from the simple
trace formulas. The Bochner integral is total and is zero for a
nonintegrable integrand.

The proof uses that the positive points have trivial projections to
finite places. The finite-place section of the norm-one group differs
from the original insertion by a positive point. The original
insertion commutes with the projection kernel by computing at each
place. Invariance of the outside function removes that insertion, and
right invariance of the normalized positive Haar measure removes the
change of positive variable.

This internal identity connects the tensor test functions used in
Arthur–Clozel, Chapter 1, §4, with orbital integrals in the Library's
norm-one group.
