# Hermitian coordinates on the actual completed CM algebra

`HermitianMatrixChart` keeps a center-preserving algebra equivalence,
an invertible Hermitian Gram matrix, and the adjoint formula for the
transported involution together. In positive matrix size,
`HermitianMatrixChart.ofEquiv` takes a center-preserving equivalence
and an involution that induces the specified nontrivial conjugation
on the center. The transported involution then acts on scalar
matrices by that conjugation, and the matrix adjoint construction
gives its Gram matrix.

`realHermitianChart` uses the comparison of the actual real scalar
extension with complex matrices and the comparison of the quadratic
center with the complex field. At a nonsplit finite place,
`nonsplitHermitianChart` uses the matrix chart coming from vanishing
upper Brauer invariants and evaluates the center at the unique upper
completion. Its coefficient involution is the transported CM
conjugation on that completion.
