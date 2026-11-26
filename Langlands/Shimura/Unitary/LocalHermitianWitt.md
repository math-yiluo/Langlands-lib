# Maximal-Witt coordinates in odd degree over a quadratic local field

The local Hermitian isotropy bound gives an isotropic vector in every
dimension at least three. Splitting off a hyperbolic plane repeatedly
leaves at most two coordinates. In odd dimension the middle block is
therefore one line. Its Gram coefficient is nonzero and fixed by
conjugation. Multiplying one endpoint in each hyperbolic pair by that
coefficient makes the whole Gram matrix a scalar multiple of the
antidiagonal Gram. The adjoint is unchanged by this scalar.

To apply the local isotropy bound with independent field universes, the
base is represented by its image in the quadratic field with the
pulled-back valuation. The field correspondence preserves the
valuation-neighborhood bases and hence local compactness. The quadratic
degree and the nontrivial conjugation agree under the correspondence.

`oddNonsplitMaxWittChart` uses this congruence in the Hermitian matrix
coordinates of the original local algebra. Evaluation at the unique
upper completion and its inverse carry the antidiagonal matrix chart
back to the original completed center. The resulting algebra equivalence
preserves the specified center inclusion and intertwines the actual
involution with the maximal-Witt adjoint.
