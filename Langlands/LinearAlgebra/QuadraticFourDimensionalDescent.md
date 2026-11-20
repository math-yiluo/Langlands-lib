# The norm and discriminant arguments in dimension four

`Langlands.QuadraticFourDimensionalDescentStatement` concerns a diagonal
four-dimensional form over a field of characteristic different from two.
Its discriminant \(d\) is the product of the four coefficients in the
coordinate basis, and is nonzero. If the expanded diagonal form over the
quadratic algebra \(K[\omega]/(\omega^2-d)\) has a nonzero zero, the form
already has a nonzero zero over \(K\). The quadratic algebra is the
Mathlib type `QuadraticAlgebra K d 0`. The assertion also applies when
this algebra splits.

The proof writes an isotropic vector over the quadratic algebra as
\(x+\omega y\). The two components of its value give
\(q(x)+d q(y)=0\) and orthogonality of \(x,y\). If \(q\) is anisotropic,
both vectors are non-null. The proof extends them to an orthogonal basis
\((x,y,z,t)\) by taking two successive orthogonal complements. The basis
construction follows Mathlib's `LinearMap.BilinForm.exists_orthogonal_basis`.
Writing \(\delta\) for the determinant of the basis change, we have
\(q(x)q(y)q(z)q(t)=\delta^2d\). Substitution gives
\(-q(z)q(t)q(y)^2=\delta^2\), so the vector
\(z+\frac{\delta}{q(y)q(t)}t\) is a nonzero zero.

Over a field \(K\) of characteristic zero with \(a\ne 0\),
`exists_eq_of_four_zero` takes a nonzero quadruple \((x,y,z,t)\) with
\(N(x+y\omega)=bN(z+t\omega)\), where \(\omega^2=a\). It gives a
representation of \(b\) by the binary norm form. If \(a\) is nonsquare,
the norm equation and the nonzero quadruple imply \(z+t\omega\ne 0\).
The quotient of the two arguments then has norm \(b\). If \(a\) is square,
the split binary norm form represents \(b\) directly.

These are derived steps for the dimension-four proof of John Voight,
*Quaternion Algebras*, Theorem 26.8.24, printed p. 451. The source passes
to the discriminant extension and uses quaternion embeddings. The Lean
proof uses the coordinate norm and the discriminant change-of-basis
identity to carry out the corresponding rank reduction and descent.
Registered source `voight-2021-quaternion-algebras`, SHA-256
`f6c56f6ca7b4bee139b88865a3cf045f899da59d0217618c4dc81daf19ef1ad4`.
