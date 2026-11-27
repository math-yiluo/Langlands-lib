# The matrix Aubert alternating sum on p-adic fields

`Langlands.Aubert.General.RationalPointFamily.GL.PadicMatrixAlternatingOperatorSpecializationStatement`
asserts that the local-field matrix functors preserve finite length and
short exact sequences after specialization to a finite extension of
\(\mathbf Q_p\). For every choice of those witnesses, the matrix
alternating sum on the exact finite-length Grothendieck group equals
`Langlands.Aubert.alternatingOperator` on the same group. Both sums use
the supplied topology, the same normalized block functors and the same
sign \((-1)^{n-k}\) for a block shape of length \(k\). Rank zero is
included.

This is a comparison of two realizations of Aubert, *Dualité dans le
groupe de Grothendieck de la catégorie des représentations lisses de
longueur finie d'un groupe réductif p-adique* (1995), Definition 1.5,
printed p. 2181 (`aubert-1995-duality`). The block shapes index the standard
parabolics, and the simple roots inside a Levi of block length \(k\) have
cardinality \(n-k\). The matrix functor comparison supplies termwise
equality of the exact class maps in the two sums.
