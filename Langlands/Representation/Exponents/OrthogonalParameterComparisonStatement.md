# Orthogonal parameter comparison

`Langlands.Exponents.OrthogonalParameterComparisonStatement` states that in
any real inner-product space, four vectors satisfying

\[
 x_1-y_1=x_2-y_2,\qquad
 \langle x_1,y_1\rangle=\langle x_2,y_2\rangle=0,
\]

and

\[
 \langle x_1,y_2\rangle\geq 0,\qquad
 \langle y_1,x_2\rangle\geq 0
\]

must satisfy both \(x_1=x_2\) and \(y_1=y_2\).

The ambient type has an arbitrary universe and the ordinary Mathlib
`NormedAddCommGroup` and `InnerProductSpace ℝ` instances. No completeness,
finite-dimensionality, nonzero-vector condition, or chosen basis is assumed.
All four vectors may vanish. The declaration is a closed proposition definition,
not a theorem asserting it.

This is an internal elementary prerequisite for later parameter comparisons.
Its justification uses the difference \(z=x_1-x_2=y_1-y_2\). Bilinearity,
symmetry, and the two orthogonality equations give

\[
 \langle z,z\rangle
 =-\langle x_1,y_2\rangle-\langle y_1,x_2\rangle\leq 0.
\]

Positive definiteness forces \(z=0\), yielding both equalities. This argument
explains the intended statement; this module supplies no proof of it.

For an application involving an orthogonal transformation, one may first
transform the first pair and then use these four vectors. Establishing the
shared difference, orthogonality, and cross-pairing inequalities from actual
representations, cuspidal support, or Jacquet exponents remains separate work.
The statement asserts no analytic continuation, chamber equality, or Langlands
data uniqueness, and imports no classification result.
