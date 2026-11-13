# Split-rank upper bound from an actual Hermitian matrix representation

This internal comparison works over arbitrary fields `K` and `L` in a common
universe, with `L/K` separable quadratic. An actual nonsingular Hermitian form
`H` on `L^N` and an injective natural matrix representation of a group scheme
`G` on every test scheme are supplied. Every represented point must preserve
the full scalar-extended Gram matrix. No determinant or image-surjectivity
condition is needed for this upper bound.

The theorem `splitRank_le_wittIndex_of_matrixRepresentation` bounds the
Library's actual split rank of `G` by the attained Witt index of `H`.
Choose a finite `K`-basis of the full matrix algebra. The all-test natural
representation gives a morphism into its finite-algebra unit group scheme;
pointwise injectivity makes the underlying scheme morphism a monomorphism.
Composing any closed standard split subtorus of `G` with this morphism is
therefore a monomorphism.

The actual matrix coordinates of the composite are exactly the supplied
representation restricted to that torus. The all-test Gram preservation
equation thus applies to the composite. The universal Laurent matrix and
weight-isotropic-subspace theorem bounds the torus's finite index cardinality
by `H.wittIndex`. Taking the four suprema over the finite index type, its
finiteness instance, the torus morphism, and its closed-subgroup proof gives
the stated bound in `ENat`.

This is derived from the existing finite-algebra matrix point comparison and
the full Hermitian weight bound. It uses neither rational-point separation
nor a characteristic restriction, and retains pairwise total isotropy in
characteristic two. It does not require affineness or finite type of `G`
and makes no classification assertion.
