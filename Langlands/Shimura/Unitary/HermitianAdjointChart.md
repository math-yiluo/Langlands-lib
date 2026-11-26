# Hermitian Gram matrices for second-kind matrix involutions

`hermitianGramOfMatrixInvolution` gives the invertible Hermitian Gram
matrix of an involution on a full matrix algebra inducing the supplied
nontrivial conjugation on the field. It includes the actual adjoint
formula for all matrices.

Compose the involution with the coefficient conjugate transpose. The
two actions on the coefficients cancel, and the composite is a field
algebra automorphism. By matrix Skolem–Noether it is conjugation by a
matrix unit. Involutivity implies that the inverse of that unit is
proportional to its adjoint. The proportionality scalar has norm one.
Multiplicative Hilbert 90 rescales the inverse to a Hermitian unit, and
the scalar rescaling cancels in the adjoint formula.
