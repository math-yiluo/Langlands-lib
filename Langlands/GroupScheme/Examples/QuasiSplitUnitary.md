# The hyperbolic unitary group of a quadratic field extension

Worker 399 constructs the group scheme using the Library's existing unitary
model. Let F and E be fields in an arbitrary universe, with E quadratic over F,
and let c be an F-algebra automorphism. The intended unitary specialization has
c different from the identity; the constructions themselves also allow the
identity. No characteristic restriction is used.

The antidiagonal Gram matrix is `gram`, and `adjoint` is its conjugate adjoint.
The lemma `adjoint_eq_gram` identifies the entry presentation with
J (c applied entrywise to M) transpose J. `matrixInvolution` packages this as an
algebra involution. `conjugation_involutive` proves that every automorphism of a
quadratic extension squares to the identity: there are at most two automorphisms,
and a nonidentity automorphism forces the automorphism group to have order two.
The chosen basis of the four-entry matrix algebra over E is retained explicitly.
`groupScheme` is exactly `SchemeModel.unitaryGroupScheme` of that basis and the
specified involution.

The presentation by the hyperbolic hermitian form
h(v,w) = v₁ c(w₂) + v₂ c(w₁) is a standard derived choice of a matrix algebra
with involution, rather than a verbatim definition from Milne. The unitary-type
algebra and its split exchange presentation are explained in Milne,
*Algebraic Groups* (2017), Proposition 24.40 and Definition 24.42, printed p.523;
the associated special unitary equation and type-A discussion are on printed
pp.524–525, including Theorem 24.44. The present group retains the full unitary
equation and imposes no determinant-one condition. The generic algebra
involution, scalar extension and represented unitary model come from the
Library, as does the tensor/matrix comparison in `ComplexMatrixSplitting`.

For every commutative F-algebra R, `scalarConjugation` sends e tensor r to
c(e) tensor r and fixes R, with the right tensor-factor R action.
`matrixPoints` is the subgroup of invertible matrices satisfying the unitary
equation, characterized by `mem_matrixPoints`. `tensorMatrixEquiv` sends
r tensor M to the matrix with entries Mᵢⱼ tensor r, intertwines involutions,
and gives `algebraPointsEquiv`. Composing with the existing represented unitary
point equivalence gives `pointsEquiv` for every test scheme, including nonaffine
and nonreduced test schemes, using its global section algebra.

`tensorCoefficientMap` applies an F-algebra map to the right tensor factor.
`tensorMatrixEquiv_changeCoefficients` proves compatibility with the Library's
coefficient change by tensor induction. `pointsEquiv_val` exposes the matrix
coordinate, and `pointsEquiv_naturality` states that restricting a point along
any morphism of test schemes applies the induced global-sections map entrywise.
Its proof composes the existing `unitaryPointsEquiv_naturality` with that tensor
calculation. Thus no affineness or reducedness assumption is added to the test
scheme.

This construction does not yet assert the dynamic subgroup identifications,
splitting, rank or reductivity.
