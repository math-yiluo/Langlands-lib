# Lipschitz bounds on orthogonal polynomial degree subspaces

`OrthogonalPolynomialLipschitzStatement` bounds the Lipschitz constant in the inherited matrix operator norm of every continuous profile of degree at most \(N\) on \(O(n)\) by \(C_n(1+N)^2\) times its supremum norm. The constant \(C_n\) is independent of the profile and of \(N\).

The proof extends the profile to a differentiable polynomial on all real matrices. In each coordinate plane, a permutation reindexes the adjacent block rotation and sends its generator to \(E_{ij}-E_{ji}\). Restriction along the corresponding right rotation has trigonometric degree at most \(N\). The finite Fourier estimate bounds the derivative at zero by \((2N+1)N\) times the supremum norm of the original compact profile. The chain rule identifies this derivative with the ambient derivative in the direction \(k(E_{ij}-E_{ji})\).

Every skew matrix is half the sum of its entries times their skew coordinate matrices. Linearity of the ambient derivative and the operator norms of the entry maps give the uniform bound in any skew direction. The Lipschitz estimate from `OrthogonalLocalLogarithm` then controls all pairs of orthogonal matrices.
