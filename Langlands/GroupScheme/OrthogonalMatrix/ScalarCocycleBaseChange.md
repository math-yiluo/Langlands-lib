# Scalar orthogonal cocycles on the pullback cover

Let `K/F` and `L/F` be field extensions and `G` the isometry group of a
scalar-involution quadratic form `q` over `F`. The map
`scalarTensorMatrixPoint` takes a point of the base change `G_K` with
coefficients in `K ⊗[F] L`, reads it as a point of `G` over the same ring,
and applies the scalar matrix chart. It preserves multiplication and the
identity.

`exists_tensor_matrix_twist` treats two cocycles on `Spec L → Spec F` in
characteristic zero. Suppose their pullbacks to the actual pullback cover
over `Spec K` differ by a pointwise twist. Then there is an invertible
matrix `a` over `K ⊗[F] L` preserving the image of `polar q`. For each
`σ : Gal(L/F)`, it relates the images of their matrix cocycle values by
`c₂(σ) = a⁻¹ c₁(σ) σ(a)`, where `σ(a)` applies the tensor Galois map to
each entry. The coefficient map on the cocycle values is the right
inclusion of `L` into the tensor ring.

The proof evaluates the pullback cocycles on two points of the cover with
coefficients in the tensor ring. The first point corresponds to the right
inclusion by the pullback adjunction. The second is obtained by
precomposition with the tensor Galois map. After forgetting `K`, their
projections to `Spec L` are the right-inclusion point and its composite
with the spectrum map of `σ`. Cocycle naturality identifies their value
with the extension of the original Galois-indexed value. Applying the
matrix chart to the cochain at the first point gives `a`, and its
naturality gives `σ(a)` at the second point.

This internal comparison uses the Library's actual pullback and ring
point maps. It works for any extension field `K`, so in particular for
each of the completions in the number-field Hasse problem.
