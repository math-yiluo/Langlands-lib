# The topology of units in a finite algebra

The unit inclusion of a finite algebra over a `T1` topological field is an open
embedding for the module topology on the algebra and the usual topology on
its units. This internal lemma supplies the passage from a continuously
varying matrix to a continuously varying unit on its invertible locus, as
used in the regular base change charts.

The proof chooses a finite basis and represents left multiplication by a
matrix. Left multiplication is invertible exactly when its determinant is
nonzero, and exactly when the algebra element is a unit. The determinant is
continuous, so the unit locus is open. The inverse of left multiplication
is continuous on that locus by the determinant and adjugate formula. Applying
this inverse to the coordinates of `1` gives the algebra inverse. Continuity
of that inverse identifies the topology on units with the subspace topology.

For a family of algebra elements tending to a unit along a filter, the open
unit locus contains the family eventually. Choosing the corresponding units
there and the identity elsewhere gives a unit-valued family with the desired
projection eventually. The embedding gives convergence in the unit topology.
