# Finite evaluation matrices

Suppose an injective linear map \(f\) takes a finite-dimensional vector
space \(V\) into scalar functions on a set \(X\). Point evaluations of
\(f\) separate vectors, so their span is the whole dual space. Select a
basis of the dual from these evaluations. The resulting evaluation map
is injective and has source and target of the same dimension, so it is
an equivalence.

`evaluationMatrix` uses the selected evaluations in the target and the
selected coordinates in \(V\). Using the evaluation equivalence of one
injective member of a family makes the matrix of that member the identity.
The same points and coordinates can then be used at every parameter.

This is the finite-dimensional reduction for the determinant argument in
R. P. Langlands, *On the notion of an automorphic representation* (1979),
Lemmas 8–9, printed p. 207, PDF p. 202 of Corvallis Part I
(`langlands-1979-notion-automorphic-representation`). Here a single injective
member suffices to choose coordinates for a determinant that is nonzero at
that parameter. To use this in a holomorphic family one must still pass
from nonvanishing at that parameter to a nonzero germ at the point of
specialization.
