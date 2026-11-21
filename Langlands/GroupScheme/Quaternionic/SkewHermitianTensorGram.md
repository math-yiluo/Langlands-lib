# Skew-hermitian row pairings in tensor coordinates

Worker 863, Task 7498.

Move scalars into the coordinates of the row space using `TensorProduct.piRight`.
The extended skew pairing is the matrix pairing using the coefficient extension
of the Gram matrix and the extended involution. The two pairings agree on pure
tensors and extend by bilinearity.

`tensorGram_exists_isotropic_with_partner` assumes an invertible Gram matrix and
an isotropic row with an invertible coordinate `i`. Multiplying the single-entry
column with the inverse of coordinate `i` by the inverse Gram matrix and applying
conjugation produces a row pairing to one with the isotropic row. The coordinate
equivalence gives tensor preimages with zero self-pairing and pairing one.

This supplies the normalized local partner in Springer, appendix to M. Kneser,
*Lectures on Galois Cohomology of Classical Groups* (1969), Theorem 5.3.3(i),
printed p. 109 (PDF p. 115).
