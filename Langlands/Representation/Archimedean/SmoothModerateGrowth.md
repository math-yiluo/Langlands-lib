# Moderate growth in the genuine derivative topology

For a jointly continuous complex Banach representation of actual real or complex general linear matrices, every continuous seminorm on the genuine smooth-vector carrier has a polynomial growth estimate. The estimate bounds the seminorm of a translate by a power of `unitHeight` times a continuous seminorm of the original vector.

The proof uses the genuine word derivatives and their inverse-conjugation covariance. An internal sequence of seminorms starts with the norm of the underlying vector. At each step it sums the preceding seminorm composed with each basis direction operator, weighted by the norm of the corresponding real basis coordinate map. These seminorms are continuous. Expanding a direction in the basis bounds the previous seminorm after differentiation by the new seminorm times the norm of the direction. Induction then bounds each word by the seminorm of its order times the product of its direction norms.

A translated word introduces one factor of `unitHeight` squared per direction through inverse conjugation. The Banach operator bound controls the remaining action after moving the translate outside the word. A continuous seminorm of the genuine derivative topology is bounded by a multiple of the supremum of finitely many word seminorms. Taking the largest order in that finite family gives a common growth exponent, and summing the corresponding weighted order seminorms gives the continuous majorant.

`wordSeminormFamily_representation_le` gives the individual word estimate
in the units of a finite-dimensional real Banach algebra. The assumed
operator bound is used at the given unit. This form also applies when
an operator bound is supplied only along the family being averaged.

`exists_seminorm_le_unitHeight_pow_of_norm_bound` obtains the continuous
seminorm majorant on the units of any finite-dimensional real Banach
algebra with a supplied polynomial bound on the Banach operators. The
general linear group case uses the Banach moderate growth theorem for that
operator bound.
