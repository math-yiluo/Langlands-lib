# Scalar quadratic forms of Witt index one over local fields

This internal consequence of the published local quadratic anisotropic
dimension bound concerns Tits's quotient-valued quadratic forms over a division
algebra `D` with `[D : K] = 1`. It retains arbitrary universes and every
characteristic.

`card_le_six_of_finrank_one_and_quadraticWittIndex_one` proves that a
nondegenerate such form with quadratic Witt index one has at most six variables.
A hyperbolic pair exists by nondegeneracy and positive Witt index. The kernel of
the two polar pairings with this pair has codimension at most two over `D`.
The published Witt-index-one argument shows that a vector in this kernel with
zero quadratic value is zero.

Choose a matrix representative of the quotient-valued form and a `K`-linear
isomorphism `D ≃ₗ[K] K`, which exists because `[D : K] = 1`. Applying this
isomorphism to the representative's self-pairing gives a scalar quadratic form.
On the kernel it is anisotropic: zero scalar value implies that the
representative's self-pairing is zero, and hence that the original quotient
value is zero. The local scalar quadratic bound gives kernel dimension at most
four over `K`. The scalar tower formula identifies this with its `D`-dimension.
Rank-nullity now gives at most six variables.

This proof uses no division by two and does not apply the trace-valued
antihermitian dimension theorem to a quotient-valued quadratic form. The import
of `LocalWittIndexOneDimension` supplies only the general ground-field bilinear
self-pairing construction `sesqFormBilinear`. This lemma will exclude division
degree one in local rank-one type `D_n` with `n ≥ 4`; it supplies no bound for
quadratic forms over quaternion division algebras.
