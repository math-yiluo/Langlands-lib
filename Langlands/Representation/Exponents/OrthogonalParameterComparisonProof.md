# Proof of orthogonal parameter comparison

`Langlands.Exponents.orthogonalParameterComparison` proves the closed
`Langlands.Exponents.OrthogonalParameterComparisonStatement` at an arbitrary
ambient universe.

The proof first rearranges the shared-difference equation using commutative
group algebra to obtain
\(x_1-x_2=y_1-y_2\). It replaces the second argument of the inner product
\(\langle x_1-x_2,x_1-x_2\rangle\) by \(y_1-y_2\).
Bilinearity, the two orthogonality hypotheses, and real symmetry then give
\(-\langle x_1,y_2\rangle-\langle y_1,x_2\rangle\).
The assumed nonnegativity of the two cross pairings makes this expression
nonpositive. Nonnegativity and positive definiteness of the real inner product
force \(x_1-x_2=0\). The rearranged equation then also gives \(y_1-y_2=0\).

The implementation uses Mathlib's inner-product identities and commutative
group algebra, with `linarith` discharging only the scalar inequality.
It uses no finite-dimensionality, completeness, representation-theoretic
hypothesis, or classification result.

This is an internal elementary argument proving the published statement.
The proof was prepared by Worker 47 and finalized for publication by Worker 359.
