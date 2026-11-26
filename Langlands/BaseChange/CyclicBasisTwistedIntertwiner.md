# Lifting twisted intertwiners using a cyclic basis

`exists_cyclicIntertwiner_lift` works with a surjective coefficient map that intertwines two
algebra automorphisms of order dividing `l`. Let `A` and `B` be the ordered norms of the two
invertible matrices `a` and `b`. Suppose that `A` and `B` have equal characteristic polynomials
and that the columns `v, Bv, …, Bⁿ⁻¹v` form a basis. A matrix in the target ring fixed by
`X ↦ a σ(X) b⁻¹` lifts to a fixed matrix in the source ring whose image is `l` times the given
matrix.

First, the identity for the `l`th iterate of `cyclicIntertwinerStep` shows that a fixed matrix
intertwines the two norms. Lift its value on `v` to a vector `w`. The matrix sending `Bⁱv` to
`Aⁱw` extends this prescription. It intertwines the norms because Cayley–Hamilton gives the
same companion matrix for their actions on the two lists of columns, via
`mul_cyclicBasisMatrix`. After reduction it agrees with the original matrix on the cyclic
basis. Finally, the sum of the first `l` iterates of the lift is fixed because the `l`th iterate
is the identity on norm intertwiners. After reduction all summands give the original matrix.
`map_cyclicNorm_of_equivariant` provides the compatibility of the ordered norm with the
coefficient map.

This is an algebraic lifting argument for the ordered norm in Arthur and Clozel, *Simple
Algebras, Base Change, and the Advanced Theory of the Trace Formula* (1989), Chapter 1, §1,
Lemma 1.1, pp. 3–4. The proof uses the cyclic-vector and Cayley–Hamilton identities from
`RegularCyclicBasis`. The registered Arthur–Clozel source `arthur-clozel-1989-base-change` has
SHA-256 `c2e47ee562810367ebcacd3f1c242eda40b9e78b271668e36d99ce31001f9a19`.
