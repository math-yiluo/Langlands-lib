# A central simple algebra tensored with its conjugate opposite

`ScalarConjugate` uses the original ring operations and the scalar map
obtained by precomposing with a field automorphism.
For an involutive automorphism, `conjugateOppositeFlip` exchanges the
factors of the algebra tensored with its conjugate opposite. Scalar
conjugation gives a balanced additive pairing on pure tensors. Reversing
multiplication in the opposite factor and exchanging the factors
make the induced map reverse products. It squares to the identity
and acts on the scalars through the specified automorphism.
For a central simple algebra, this is an involution of the second kind
when the automorphism acts nontrivially on the field.

`exists_unitaryInvolution_of_brauerEquivalent` transports existence
across matrix-stable equivalence with the same prescribed nontrivial
automorphism of the center. Extend the involution by transpose
to the matrix algebra on the source. Transport to the target and use
its Wedderburn decomposition to view it as matrices over a division
algebra. The division-corner theorem supplies an involution there.
Transpose over that division involution and transport back to the
original target algebra.

The conjugate algebra is the scalar twist used in Knus, Merkurjev,
Rost and Tignol, *The Book of Involutions*, §3.B, printed pp. 36–37.
Here the opposite in one factor produces an anti-automorphism. The
matrix-stable existence assertion is also the final assertion of
Theorem (3.1), printed p. 31. The registered source
`knus-merkurjev-rost-tignol-1998-book-of-involutions` has SHA-256
`e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`.
