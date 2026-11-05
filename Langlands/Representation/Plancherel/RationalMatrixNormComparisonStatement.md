# Power comparison for actual rational-point matrix norms

`Langlands.Plancherel.RationalMatrixNormComparisonStatement.{u}` states a
polynomial bound between the actual rational-point matrix norms of two
algebraic matrix representations of the same group scheme over an arbitrary
nonarchimedean local field `F : Type u`.

The source representation `ρ` is a supplied closed embedding into the explicit
general linear group scheme. The target representation `τ` is any algebraic
matrix representation. Both finite matrix index types lie in `Type` and are
nonempty, as in the assigned coefficient-growth target. No connectedness,
reductivity, splitness or characteristic hypothesis is imposed on the group
scheme. There is no representation carrier in this statement.

The conclusion chooses a natural number `d` and a strictly positive real `c`
before all actual rational points `g`, and asserts
`rationalMatrixNorm F τ g ≤ c * rationalMatrixNorm F ρ g ^ d`.
The norm is exactly the residue-normalized matrix norm from
`RationalModerateGrowthStatement`, including entries of the inverse matrix.
Applying the assertion twice compares two supplied closed embeddings in both
directions. This file states the comparison and contains no proof of it.

This is an internal algebraic prerequisite for the assigned coefficientwise
moderate-growth proof. Its intended derivation lifts regular functions through
a closed immersion, presents general-linear coordinates as a quotient of the
polynomial ring in matrix and inverse entries, bounds finitely many
polynomials, and uses inverse invariance. It is not claimed to be a verbatim
statement in the original literature. The comparison alone supplies no
coefficient-growth bound or structural decomposition of the rational group.
