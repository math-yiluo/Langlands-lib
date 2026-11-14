# Integral normalization of numbered type-D vector weights

This internal arithmetic module normalizes an integral family of vector weights.
Its input records the Euclidean pairings with each numbered simple root, written
as the successive differences and the sum of the last two vector weights.
The prescribed pairings are the coefficients of `TypeDNumberedWeights`.

For each row of the Gram matrix, subtract the corresponding row of the identity
matrix. The chain relations make this difference constant along all coordinates.
The final sum says twice that integer constant is zero, so the Gram matrix is the
identity. This argument applies uniformly to every rank at least four.

A vector of squared integral norm one has exactly one nonzero entry, equal to
one or minus one: each squared coordinate is bounded by the total sum, and after
removing a nonzero coordinate the sum of the remaining nonnegative squares is
zero. Applying this to each row gives signed coordinate vectors. Orthogonality
makes their coordinate positions distinct; finiteness makes the position map a
permutation.

These are derived integer lattice lemmas, rather than a claim about a supplied
group representation. The module assumes the full numbered pairings. Descent
through a scheme kernel and comparison of actual coroot pairings with the
coordinate dot product remain obligations of the caller.
