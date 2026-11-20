# Local-to-global quadratic isotropy from cyclic Hasse norm

Workers 787 and 864.

`Langlands.NumberFieldQuadraticIsotropyOfCyclicNormStatement.{u}` says
that the cyclic Hasse norm theorem on actual ideles implies local-to-global
isotropy for nondegenerate quadratic forms over number fields.
`Langlands.numberFieldQuadraticIsotropy_of_cyclicNorm` proves the
implication.

For a four-variable diagonal form over a field of characteristic zero,
assume every coefficient \(w_i\) is nonzero and let \(d=\prod_i w_i\)
be its discriminant. When \(d=s^2\), divide by \(w_0\) and scale the
last coordinate by \(s/(w_1w_2)\). With
\(a=-w_1/w_0\) and \(b=-w_2/w_0\), the equation becomes
\(x^2-ay^2=b(z^2-at^2)\). A nonzero solution implies a solution of
\(X^2-aY^2=b\) by `QuadraticFourDimensionalDescent.exists_eq_of_four_zero`.
Conversely, a solution of this norm equation gives a zero of the
four-variable form by taking \(z=1\) and the last coordinate zero.
These two implications at the completions and over the number field
reduce the square discriminant case to the local-to-global norm equation.

Over a number field, if \(d\) is nonsquare, adjoining a generator of
square \(d\) gives a quadratic number field extension. The completion
embeddings preserve local isotropy, and the generator witnesses the
square discriminant. The solution over this extension descends by the
proved discriminant descent theorem.

The conditional norm result also supplies the rank-three case. Square
reflection gives rank two, while nondegenerate forms of ranks zero and
one have no nonzero isotropic vectors over any completion. The
higher-rank step applies weak approximation to
the first two coordinates and inducts on dimension. Orthogonal
diagonalization and the tensor scalar extension comparison transfer the
result back to the original vector spaces.

The provenance is the same dimension argument as in John Voight,
*Quaternion Algebras*, Springer, 2021, Theorem 26.8.24, printed p. 451.
Source ID `voight-2021-quaternion-algebras`, SHA-256
`f6c56f6ca7b4bee139b88865a3cf045f899da59d0217618c4dc81daf19ef1ad4`.
The implementation uses cyclic Hasse norm for the norm equation and
quadratic basis computations for the rank-four descent.
