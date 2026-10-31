# Transport of actual bi-smooth matrix coefficients

This is an internal development from the published matrix coefficient,
smooth-vector, and smooth-dual definitions. It provides the coefficient step
needed for the inverse-transpose branch of conditional Godement–Jacquet
analytic induction. No analytic-existence result is proved.

`coefficientPullback φ` is complex-linear precomposition of scalar functions
by a group homomorphism. For a continuous homomorphism, the original smooth
vector and smooth functional remain smooth for the pulled-back action.
The proof uses the inverse image of their fixing open subgroups. For the
functional, the shared `Langlands.dual_comp_monoidHom` from
[`Smooth.Transfer.GroupEquivalence`](../Smooth/Transfer/GroupEquivalence.md)
checks that the algebraic dual action commutes with pullback, using preservation
of inverses. The same module supplies
`isSmoothVector_comp_continuousMulEquiv_iff` and
`isSmoothVector_dual_comp_continuousMulEquiv_iff`.
`map_biSmoothMatrixCoefficients_le` extends this construction from generating
coefficients to their entire complex span.

For a continuous group isomorphism, applying the same argument to its inverse
proves the converse smoothness implications.
`biSmoothMatrixCoefficients_comp_equiv` proves equality of the full pulled-back
coefficient submodule with the image of the original submodule.
`forall_biSmoothMatrixCoefficients_comp_equiv` expresses this equality as a
transport rule for arbitrary predicates on the coefficient functions.
Neither statement assumes the whole representation is smooth or admissible.

`biSmoothMatrixCoefficients_equiv` proves that an equivalence of
representations preserves their coefficient submodules. Given a coefficient
of the target, pull its functional back along the equivalence and its vector
back along the inverse equivalence. The published smoothness transfer for
intertwiners shows that both are smooth. Equivariance gives the original
coefficient pointwise. Applying this in both directions gives equality of
the submodules. The ordinary and inverse-transpose rational-value families,
and both full analytic predicates, therefore agree across a representation
equivalence. The proofs rewrite only the coefficient family.

Finally, `iotaMatrixRationalValues_eq_comp_inverseTranspose` identifies the
published transformed value set with the ordinary value set of the actual
inverse-transpose pullback action.
`iotaMatrixAnalyticAssertions_iff_comp_inverseTranspose` proves the analogous
equivalence for the complete analytic predicate. For convergence, it uses the
same real bound and the universal coefficient transport rule for each test
function. The same rule transports actual rational continuation for every
test and coefficient. The value-set equality then transports the normalized
generator property. The spectral variable, shift, measure, tests, polynomial,
and denominator guards inside rational continuation are unchanged.

The inverse-transpose action is the published continuous automorphism
`GeneralLinear.inverseTransposeContinuous`. This argument does not identify
the transformed family with a smooth contragredient coefficient space and
requires no irreducibility assumption. Its provenance is the elementary
transport argument above, rather than an additional theorem translated from
the literature. The application to normalized induction, including its ordered
dependent family, is in `InverseTransposeProductAnalytics`.
