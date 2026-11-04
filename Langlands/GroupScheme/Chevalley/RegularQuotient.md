# Coordinate restriction on finite regular representations

This is an internal derived construction from the coalgebra, actual coordinate
restriction and finite regular representation interfaces. It supplies part of
the ambient representation extension argument; it does not prove that extension
theorem or the Cartan-generation statement.

For a linear map `q : B →ₗ[k] C`, finite subspaces `V ⊆ B`, `W ⊆ C`, and chosen
finite bases, `regularQuotientMatrix` has columns equal to the extended basis
coordinates of `q(bV j)` in `W`. If `W = V.map q`, its associated linear map is
surjective. The proof expands a chosen lift of a vector of `W` in the basis of
`V` and applies the extended coordinates in `W`.

For coalgebra maps, `rightAct_coalgHom` states that contraction in the second
factor commutes with the map after pulling the functional back. Tensor induction
proves this identity. It implies `rightAct_mem_map`: the image of a subspace
stable under all right contractions remains stable. Applying the coalgebra map
to the basis comultiplication formula gives `regularQuotientMatrix_mul`, the
matrix equivariance equation for the regular coactions whenever `q(V) ⊆ W`.

For actual corepresented group functors `H → F` over an arbitrary field of
universe `u`, `universalMatrix_restrict` says that restricting an actual matrix
representation evaluates its universal coefficients by `coordinateRestriction`.
This follows from affine matrix restriction and the classified affine point.
`intertwines_regularQuotient` then turns the preceding coaction equation into an
actual intertwiner between the restricted ambient regular representation and
the subgroup regular representation. The equation holds on every affine algebra
test, by the universal-point criterion from `CoefficientEmbedding`.

Finally, `exists_finite_regular_lift` assumes that the actual map is a closed
subgroup inclusion. Surjectivity of its coordinate restriction lifts any given
finite coordinate family. The finite regular span of the lifts is stable under
all right contractions, and its image contains the original family. This step
does not require finite type, smoothness, connectedness, infinitude, perfection,
or a splitting assumption. Empty finite families and zero-dimensional subspaces
are allowed.
