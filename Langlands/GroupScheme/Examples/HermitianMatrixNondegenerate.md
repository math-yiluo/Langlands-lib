# Gram coordinates and Hermitian nondegeneracy

This is internal elementary linear algebra for the actual nonsingular Gram form in `HermitianMatrixBasic` and its pairing in `HermitianMatrixPairing`. The coefficient ring is an arbitrary commutative ring with a specified involution; the finite index type and coefficient ring have independent arbitrary universes. No field or characteristic restriction is imposed.

`Form.gramCoordinates` is the linear equivalence given by multiplication of column vectors by the stored invertible Gram matrix. It uses Mathlib's equivalence between invertible matrices and linear automorphisms, and `gramCoordinates_apply` states its actual matrix value.

`pairing_eq_dotProduct` rewrites the implemented finite double sum as the dot product of the conjugated first vector with the Gram matrix times the second vector. `linearFirst_eq_dotProduct` gives the corresponding formula after flipping the arguments: `H.linearFirst x y` is the dot product of the conjugated `y` with `H.gram.mulVec x`. These are finite-sum identities, with the same conventions as the existing split-rank matrix presentation.

`pairing_single_left` evaluates the first argument at a standard coordinate vector. If a vector pairs to zero against every first argument, these evaluations show that its image under the Gram matrix is zero. Invertibility of the actual matrix then gives the zero vector, as stated by `eq_zero_of_pairing_right`. Hermitian symmetry gives `eq_zero_of_pairing_left`. The two conclusions are bundled as `sesquilinear_nondegenerate` and `linearFirst_nondegenerate`, using Mathlib's two-sided nondegeneracy predicate. The proof uses no Witt decomposition, rank theorem or classification.
