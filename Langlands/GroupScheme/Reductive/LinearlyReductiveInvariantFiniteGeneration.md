# Hilbert finite generation for linearly reductive group schemes

The theorem `Langlands.GroupScheme.linearlyReductiveInvariantFiniteGeneration`
proves exactly the published proposition
`Langlands.GroupScheme.LinearlyReductiveInvariantFiniteGenerationStatement`
in every universe. Over an arbitrary field, semisimplicity of every finite
matrix representation gives finite generation of the algebra of polynomials
invariant on every scheme test.

`invariantIntegralOfLinearReductivity` constructs a normalized invariant
coordinate integral from the target's simple-span hypothesis.
`PolynomialAverage.reynolds` uses it to average inverse translates at the
universal point. The resulting linear map takes values in the invariant
subalgebra, fixes its elements, and commutes with multiplication by them.

The invariant subalgebra is closed under homogeneous components.
`subalgebra_fg_of_graded_reynolds` uses Noetherianity to choose finitely many
positive-degree homogeneous invariants generating their ideal in the polynomial
ring. It applies the projection to an ideal expression and takes homogeneous
components to reduce to invariant coefficients of strictly lower degrees.
The degree-zero case consists of scalars. The proof then uses
`invariantPolynomialSubalgebra_fg_iff` to obtain the finite set of invariant
polynomial generators required by the target.
