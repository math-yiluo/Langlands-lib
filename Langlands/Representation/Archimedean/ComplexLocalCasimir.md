# The real trace Casimir for the local complex general linear group

The real trace form on the complex matrix Lie algebra is
\((X,Y)\mapsto\operatorname{Re}\operatorname{Tr}(XY)\).
Trace cyclicity proves invariance. Pairing with a transposed matrix unit
and its imaginary multiple detects the real and imaginary parts of each
entry, so the form is nondegenerate.

In the real basis of matrix units \(E_{ij}\) and \(\mathrm{i}E_{ij}\),
the trace-dual directions are \(E_{ji}\) and \(-\mathrm{i}E_{ji}\).
The published invariant-form construction puts the resulting Casimir in
the center of the enveloping algebra of the real Lie algebra's
complexification. The proof checks commutation with the real generators
and extends it to complex tensors and their generated algebra.

The right-coordinate square sum adds the squares of all real basis
directions. The compact square sum is one quarter of the sum over
ordered pairs \(i,j\) of the squares of the skew-Hermitian directions
\(E_{ij}-E_{ji}\) and \(\mathrm{i}(E_{ij}+E_{ji})\).
Expanding the squares in the enveloping algebra and exchanging \(i,j\)
in the sums gives the coordinate square sum as the trace Casimir plus
twice the compact square sum. This is the local matrix calculation
corresponding to `ArchimedeanCasimirCartan.lean`.
