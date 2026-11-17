# Determinant transitions of bases adapted to a split surjection

Let `R` be a commutative ring, `V` and `W` be `R`-modules, and let
`f : V →ₗ[R] W` admit a specified linear section `s`, with
`f (s w) = w`. All module and basis index universes are independent.

This is an internal linear-algebra construction for assembling the actual
augmentation-jet filtration. It uses Mathlib's product basis, matrix of a
basis transition, and determinant of a block triangular matrix. It adds no
external source claim.

`kernelProjection f s hs` sends `x` to `x - s(f x)` in the actual kernel
of `f`. `splitEquiv f s hs` is the resulting linear equivalence
`V ≃ₗ[R] W × ker f`, with inverse `(w,k) ↦ s(w)+k`.
The inverse identities are proved directly from the section identity.

For a second linear section `t`, `sectionDifference f s hs t ht`
is the linear map `w ↦ t(w)-s(w)` into the actual kernel.
`splitEquiv_apply_symm` computes the change of the two product
decompositions as `(w,k) ↦ (w, (t-s)(w)+k)`.

`adaptedBasis f s hs b c` transports the product of a basis `b` of `W`
and a basis `c` of `ker f` through the inverse product decomposition.
For a second quotient basis `b'`, kernel basis `c'`, and section `t`,
`adaptedBasis_toMatrix` gives its transition matrix as

`[[b.toMatrix b', 0], [D, c.toMatrix c']]`,

where `D(k,i)` is the `c` coordinate at `k` of
`(t-s)(b' i)`. The proof computes product-basis coordinates using the
preceding product-decomposition formula.

For finite basis index types, `adaptedBasis_toMatrix_det` proves that the
determinant transition is
`det(b.toMatrix b') * det(c.toMatrix c')`. It applies Mathlib's
block-triangular determinant formula to the computed matrix. Thus this
determinant is independent of both section choices. No projectivity or
finite-generation assumption is needed beyond the supplied sections and
bases; finiteness of the basis indices is used for the determinant.
