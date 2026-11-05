# Internal polar factors and maximal compact subgroups

Author: Worker 1571.

This internal auxiliary module combines `AlgebraicPolar.exists_positive_sqrt`
with the compactness and maximality results of `ClosedPolarCompact`. The field
is any `RCLike` field in universe `u`. Matrix factors are constructed for every
finite index type `n : Type`, including the empty type. The representation
corollaries use `Fin d` and allow the represented group to have an independent
universe `v` and an arbitrary given topology.

For a subgroup `H` of matrix units, polynomial equations in both matrix entries
and inverse entries must characterize membership exactly, as specified by
`AlgebraicMatrixPowers.IsPolynomiallyDefined`. The other algebraic hypothesis
is closure under the matrix adjoint, expressed using `star` on matrix units.
For `g` in `H`, the product `star g * g` is positive definite and remains in
`H`. The imported square-root theorem supplies a positive definite `a` in `H`
with `a * a = star g * g`. Its Hermitian property gives `star a = a`, and
`k = g * a⁻¹` is unitary by this square equation. Subgroup closure keeps `k`
in `H`, giving `g = k * a`.

Applying that factorization to `star g` and taking adjoints gives the opposite
order `g = a * k`, with the same positivity and unitary conditions. For an
injective representation whose range satisfies the two algebraic hypotheses,
choosing preimages of both factors and using injectivity transports each
factorization to the original group. The left positive factorization also
shows that every `g` has a unitary `k` for which the right quotient `g * k⁻¹`
has positive definite matrix image.

`maximalCompactOfPolynomialStarClosed` takes a representation that is a closed
topological embedding, together with these polynomial and adjoint hypotheses.
It constructs the inverse image of the standard unitary group and proves it
compact and maximal among all compact subgroups containing it. The
construction supplies the transported positive factors to
`maximalCompactOfClosedPolar`, using positive definiteness to obtain its
positive semidefiniteness premise. The resulting subgroup is the existing
`MatrixPolarCompact.unitarySubgroup`.

The proof uses the imported spectral square-root construction and elementary
adjoint group identities; this module introduces no new literature assertion.
It remains conditional on the representation and its algebraic properties.
It does not establish an adjoint-compatible realization of actual reductive
scheme points, or the actual parabolic covering required by
`InfinitePlaceGroupPoints.ParabolicIwasawaStatement`.
