# Explicit jet embeddings for actual affine parabolic quotients

Over an arbitrary affine base, `ProperQuotientJetData` records a coordinate
ideal for an actual smooth closed subgroup with geometrically connected
fibres, a finite stabilizing jet order, the finite projective ambient and
subgroup jet modules, and the explicit Grassmannian closed embedding of a
supplied proper homogeneous quotient. The ideal cuts out the actual subgroup
on every test scheme, and the recorded stabilizer equality holds over every
base algebra. The embedding uses the original quotient projection composed
with the affine coordinate isomorphism; it does not replace the supplied
quotient scheme.

`properQuotientJetData` constructs these data for a smooth affine group and a
smooth closed subgroup with geometrically connected fibres that equals its
full normalizer. This reuses the coordinate and finite-stabilization argument
of `selfNormalizingProperAmbient`, retaining its ideal and jet data. Smoothness
makes the coordinate algebra smooth. The closed subgroup ideal has smooth
quotient and geometrically integral field fibres. Self-normalization and the
finite generation of this ideal supply a single stabilizing jet. Smooth
augmentation jet quotients are finite projective over the arbitrary base.
The homogeneous quotient's exact all-test coset fibres, transported through
the coordinate group isomorphism, are precisely the stabilizer fibres.
`quotientJetEmbeddingData` then constructs its actual closed embedding and
retains the explicit orbit factorization.

`affineParabolicQuotientJetData` applies this construction to the existing
`affineParabolicQuotient` of a relative parabolic in a reductive group. The
published parabolic closedness, geometric connectedness and self-normalizer
theorems supply the subgroup inputs; the existing quotient supplies properness.
No extra noetherian, splitting, rank, or field-type premise is added.

This internal refinement combines existing coordinate, stabilization and
quotient theorems. It does not assert a comparison with the universal
conjugate family's identity jet sheaf or an identification of its determinant
with a positive power of the Lie determinant dual. Those remain separate
inputs to the determinant ampleness argument.
