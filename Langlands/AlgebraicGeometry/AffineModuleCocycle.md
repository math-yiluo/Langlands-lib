# Natural affine cocycles with module coefficients

This internal helper formulates natural additive cocycles on pairs of
algebra points of an affine cover with values in scalar extensions of one
arbitrary coefficient module. The coefficient module need not be free,
projective, or finitely generated.

For a faithfully flat algebra `A → B`, a cocycle evaluated on the two
universal maps `B → B ⊗[A] B` gives a tensor with coefficients. Naturality
and the cocycle relation identify its three faces with the alternating
Amitsur differential. The implemented associativity comparisons identify
this differential with the published arbitrary-module differential in
`FaithfullyFlatAmitsurDegreeOne`. Its exactness supplies a primitive.
Naturality for the product of two algebra maps then gives the
coboundary identity on every algebra.

The sign of the primitive is chosen so that the resulting coboundary is
the first pullback minus the second pullback. This is a derived
algebraic helper for the affine vector-bundle torsor argument; it does
not assert representability, geometric filtration existence, or the
affine Levi existence target.
