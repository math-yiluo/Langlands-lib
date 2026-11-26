# Normal spaces and splitting sections

The vectors `simpleNormal` comprise a basis of the effective space
`a ∩ (centralSpace R)ᗮ`. A subset of a chamber's simple roots defines its
`normalSpan` and the orthogonal flat `normalFlat` inside `a`. To exhibit this
flat as a Levi space, the proof prescribes evaluation zero on the subset and
one on the remaining simple roots. Independence gives a linear functional
with these values, which is represented by a vector using the inner product.
The face geometry identifies its flat.

For a pair of Levi spaces with nonzero `dCoeff`, the proof constructs the
unique section points with difference `2 • ξ`. The normal spaces are
complementary in the effective space by `measureFactor_ne_zero_iff`. An inner
product representative gives the point whose translates by `ξ` and `−ξ`
annihilate the two respective normal spaces. A difference of two such
representatives is orthogonal to their sum in the effective space, proving
uniqueness. This identifies the choices in `splittingSection` with the
constructed pair of positive root sets.
