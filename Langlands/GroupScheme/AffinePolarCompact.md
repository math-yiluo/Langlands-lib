# Polar compact subgroups on actual affine points

Authors: Worker 1571 and Worker 1359.

Let `k : Type u` be a field, `S : Type u` an `RCLike` field equipped with a
`k`-algebra structure, and `G` an affine actual group scheme over `Spec k`.
Let `ρ : MatrixRepresentation G (Fin d)` be a scheme-theoretic closed
representation. The natural number `d` may be zero. The source of every
coefficient map here is literally `G.affinePoints (CommAlgCat.of k S)`,
with its existing regular-function evaluation topology.

`affineUnitarySubgroup` is the inverse image of the ordinary unitary
matrix group under the actual coefficient homomorphism `ρ.affineMatrix`.
Its membership lemma states the unitary condition on the coefficient matrix
itself. `isCompact_affineUnitarySubgroup` uses the existing closed topological
embedding theorem for that same map and compactness of the ambient unitary
matrix group. In particular, no replacement of the actual point carrier or
topology is involved.

Suppose the image of `ρ.affineMatrix` is stable under conjugate transpose.
`exists_affineUnitary_right_quotient_posDef` proves that for every actual point
`g` there is an actual point `a` in this unitary subgroup such that the
coefficient matrix of `g * a⁻¹` is positive definite. The polynomial-image
comparison proves polynomial definability directly from the scheme-theoretic
closed immersion. The imported internal polar-factor theorem then applies,
using injectivity of the existing closed topological embedding to transport
the factors back to actual points.

`affineMaximalCompact` constructs a subgroup with compactness and unrestricted
compact-overgroup maximality. Its underlying subgroup is exactly
`affineUnitarySubgroup`, as the value lemma records. The construction applies
`InternalPolarFactors.maximalCompactOfPolynomialStarClosed` to the actual
coefficient map. Its closed embedding comes from
`InfinitePlaceMatrixRealization`; its polynomial equations come from
`MatrixRepresentationPolynomialImage`. The imported proof obtains internal
polar factors by taking the positive square root of `g* g`; compact
positive-semidefinite rigidity then forces every compact overgroup of the
unitary inverse image to equal it.

This is an internal composition of those matrix and actual-point results.
It supplies neither the existence of a self-adjoint representation for an
arbitrary connected reductive group nor a parabolic covering. Adjoint
stability is an explicit hypothesis of this auxiliary construction. The
closing actual archimedean Iwasawa theorem still has to establish all its
conclusions from its original hypotheses without this additional premise.
