# Extending matrix linear maps

This internal construction extends a linear endomorphism of matrices along any
homomorphism of commutative coefficient rings. It uses the matrix units as a
basis: each image matrix unit is mapped to the new coefficient ring, and the
result is extended linearly over that ring.

The bundled map is linear over the new ring. `extendMatrix_map` proves that its
value on a matrix from the original ring is the coefficient image of the
original linear map. The proof expands a matrix in matrix units and uses
additivity and scalar compatibility.

`map_extendMatrix` proves naturality under another coefficient homomorphism.
`extendMatrix_eq` identifies the extension with any linear map over the new
ring that agrees on all matrices from the original ring. The proof uses the
images of matrix units and expands an arbitrary matrix in those units.

The construction and proofs are derived elementary linear algebra, supporting
the adjoint action and the descent of inner forms; no classification is asserted.
