# Archimedean Lie and enveloping maps for two diagonal blocks

For a rank decomposition \(a+b=n\), `blockDiagonalMatrixMap` inserts a pair of matrices over the mixed real and complex space into the diagonal blocks of a matrix of rank \(n\). The multiplication identity makes it a homomorphism for the commutator Lie brackets. The first and second real block inclusions place the given input in its own block and zero in the other. Extending scalars to \(\mathbb C\) and applying the universal enveloping functor gives the two maps on the actual enveloping algebras. The pure tensor and generator formulas identify these maps on the directions used for differentiation.

`centralIdealRightSpan` is the complex linear span of products with an element of the given center ideal on the left and an arbitrary enveloping element on the right. This packages the part of the ambient operator algebra that acts by zero when the ambient center ideal annihilates a vector, since the central factor commutes with the other operator.

The constructions implement the inclusion of the Levi enveloping algebra and the ambient central ideal used in the constant-term argument of Harish-Chandra, *Automorphic forms on semisimple Lie groups* (1968), Chapter I, §6, proof of Theorem 1, printed pp. 19–20, PDF pp. 29–30.
