# Smooth matrix derivatives control compact differences

Work with a smooth function on the real space of complex matrices. Its
restriction to the unitary group has compact right differences controlled
by the real matrix derivatives on the convex hull of the unitary group.
This convex hull is stable under right multiplication by a unitary
matrix. The operator norms of unitary matrices, and consequently the
norms of all matrices in their convex hull, have a uniform bound.

For one right difference, the derivative of a linear precomposition
changes both the base point and the multilinear arguments. The mean
value estimate on the convex hull bounds the first change by the norm
of the next derivative times the base point displacement. The
multilinear argument estimate bounds the second change by the norm of
the derivative times the displacement of right multiplication as a
linear operator. Each displacement has a factor equal to the matrix
norm of the unitary move minus the identity.

Iterate the derivative estimate along the list of right moves, using
one more derivative for each move. The zeroth derivative then gives a
bound for the iterated compact difference with one displacement factor
per move. The same bound applies to the standard-module difference
when the restricted function is the compact profile of a standard
vector.

The one-move estimate also applies on any convex set containing both
base points, with uniform derivative bounds on that set and a common
norm bound for the starting point and the unitary move.
