# Globalization of supercuspidal representations of `GL_n`

`generalLinearSupercuspidalGlobalization` proves
`GeneralLinearSupercuspidalGlobalizationStatement.{u, w}`. In positive rank,
`exists_supercuspidalCommonVector` constructs a nonzero vector in the actual
cuspidal `L²` space. The test is a compact adelic tensor of inverse matrix
coefficients at the prescribed places, with the integral factors away from
them and a cutoff at the supplied auxiliary place. The cutoff isolates the
identity term in the periodization after positive averaging. Convolution
against the conjugate periodization gives the nonzero vector. The local
Jacquet conditions and the cuspidal-image theorem give cuspidality, and
the integral factors give the required common level. Varying one local
vector at a time puts the common vector in the image of an intertwiner
for each prescribed determinant-unit subgroup.

`generalLinearFullAEL2CuspidalCompactness` gives compactness of continuous
compactly supported convolutions on this cuspidal space.
`groupSchemeFullAEL2CuspidalDecomposition` gives an orthogonal Hilbert sum of
irreducible subspaces, whose span is dense by surjectivity of its sum
isometry. `extract_supercuspidalSummand_of_determinantUnitOccurrence` takes a
summand where the projection of the common vector is nonzero. Equivariance
of the projection preserves its level and makes the projected local maps
nonzero. The unitary Schur theorem and extension from determinant-unit
groups give the original local embeddings up to unramified determinant
twists.

`generalLinearSupercuspidalGlobalization_of_positiveRankOccurrence` handles
rank zero separately and applies the per-summand local trace factorization
to these embeddings. For each prescribed place and each pair of Haar
measures it gives one complementary functional valid for all the stated
test pairs with trace-class compression.

The proof uses the cuspidal-image criterion of Getz–Hahn, *An Introduction
to Automorphic Representations* (2024), Definition 16.4.1 and Lemma 16.4.2,
printed p. 430. The compact test construction and determinant-unit
intertwiners are described in `GeneralLinearSupercuspidalCommonVector`.
