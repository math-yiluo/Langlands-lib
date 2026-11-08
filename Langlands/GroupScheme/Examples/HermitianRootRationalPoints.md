# Rational points and generation of the weighted Hermitian scheme model

This internal construction uses the actual weighted Hermitian group scheme
over a separable quadratic extension `L/k`, with both fields in an arbitrary
common universe. The middle index is a finite type in the lowest universe.
The supplied diagonal Hermitian form `H` has actual unit middle weights
`w i`. The rational-point comparison imposes no anisotropy or characteristic
restriction.

The existing `SU3Root.SchemeModel.baseAffineTest` is the actual affine test
scheme associated to the base coefficient algebra. Its existing
`rationalCoefficientEquiv` evaluates the actual tensor coefficient ring
back into `L` and commutes with quadratic conjugation.
`rationalCoefficientEquiv_weight` uses its `L`-algebra structure to prove
that every included middle weight evaluates to the original weight.

The multiplicative equivalence `rationalMatrixEquiv` composes the existing
canonical rational-point/base-affine-test comparison, the all-test point
comparison for the weighted group scheme, and the compatible-coefficient
equivalence on the full determinant-one isometry groups.
Its target is the actual subgroup of invertible matrices over `L`
preserving the full weighted Hermitian Gram matrix and having determinant
one. `rationalMatrixEquiv_val` proves that this matrix is obtained by
evaluating, entry by entry, the tensor matrix of the actual ambient
inclusion.

The homomorphisms `rationalUpper` and `rationalLower` transport the actual
upper and opposite root embeddings through this equivalence. The two
matrix-coordinate formulas identify them with those original embeddings.
Their injectivity follows from the previously proved matrix-embedding
injectivity.

The generation results additionally assume `H.IsAnisotropic`: a middle
vector with zero self-pairing must be zero. The existing nonidentity
quadratic conjugation supplies a nonfixed scalar in every characteristic.
The earlier full matrix-generation theorem therefore identifies the
elementary subgroup with the actual determinant-one isometry subgroup.
For `eq_top_of_rational_roots`, map a supplied rational-point subgroup
into the ambient general-linear group through `rationalMatrixEquiv`.
Containment of both root ranges implies containment of their generated
elementary subgroup. Matrix generation then puts every rational point
in this image, and injectivity returns its membership in the original
subgroup. Applying this criterion to the join of the two root ranges
proves `rational_root_ranges_eq_top`.

The provenance is internal: actual tensor evaluation, the established
weighted all-test isometry comparison, and the established anisotropic
middle matrix generation. The tensor evaluation and its conjugation
compatibility are reused by Lean name from the existing SU3 model.
Smoothness, reductivity, identification of the root images with rational
parabolic radicals, and the unrestricted local Kneser–Tits theorem remain
separate obligations.
