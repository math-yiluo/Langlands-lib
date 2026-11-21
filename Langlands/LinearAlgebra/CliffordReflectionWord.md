# Clifford units of quadratic reflection words

Let `Q` be a quadratic form on a vector space over a field. A vector of nonzero value defines a Clifford unit. Multiply the Clifford vectors in reverse list order so that their successive conjugations agree with the order of application in `reflectionWord`.

`reverse_mul_cliffordReflectionWord` evaluates the product of the reversion and the word as the scalar product of the quadratic values in the list. `cliffordReflectionWord_conj` computes its action on a vector as the reflection word multiplied by the sign of the length. The sign is one for an even list. No finite-dimensionality or nondegeneracy of the ambient form is needed for these identities.

The single-vector identity follows from the Clifford anticommutator and the reflection formula. The word identities follow by induction. These are the Clifford calculations used to relate reflection products to the spinor norm in the exact sequence of Kneser, *Lectures on Galois Cohomology of Classical Groups* (1969), §5.11, p. 99.
