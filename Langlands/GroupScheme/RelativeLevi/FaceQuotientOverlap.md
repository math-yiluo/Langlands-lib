# The original quotient on a common affine parameter

If an affine parameter factors through a chart of the finite cover, `globalFaceQuotientAffineIso` identifies the pullback of the global quotient with the standard vector group of that chart's layer rank over the parameter ring. It composes the original parameter recovery with the canonical change of coefficients for a standard vector group. `globalFaceQuotientAffineIso_projection` identifies the original pulled-back quotient projection in these coordinates.

For two factorizations of the same map to the base, `globalFaceQuotientAffineIso_overlap` compares the two isomorphisms by the canonical `restrictionQuotientIso`. The ambient inclusion of the second restricted term is monic, so the recovered ambient squares identify the two term maps after the canonical term comparison. The original global quotient remains a full fppf quotient on the parameter. Its uniqueness on homomorphisms then identifies the quotient maps using their projection squares.

`VectorGroup.coordinates_affineCoefficientIso_hom` identifies the coordinates on a scheme test before and after the canonical coefficient isomorphism. Its proof writes the given affine morphism as the spectrum of the corresponding ring map and uses the coordinate formula for base change.

These internal comparisons follow from the actual term and quotient squares and the coefficient normalization. The parameter ring may be zero, and the two layer ranks are the ranks prescribed by their original charts.
