# Splitting vector extensions by invariant coordinate integration

This internal construction generalizes the implemented averaging proof in
`Rational.SplitTorusVectorExtension` to an arbitrary affine quotient group
with a supplied `CoordinateIntegration.InvariantIntegral`. It retains a
scheme section, a monomorphic presentation of the full vector kernel, and
natural linear coordinates for ambient conjugation as explicit inputs.
It neither constructs an invariant integral for a reductive group nor proves
the characteristic-zero reductive vector-extension statement.

The contraction is linear over the coefficient algebra, so it commutes with
finite matrices over that algebra. Naturality of the actual action matrix
then makes averaging commute with ambient conjugation. The construction
integrates the actual section defect against the universal point in the
second coordinate factor. Translation invariance, normalization on constants,
and the defect cocycle identity show that this average is a regular
coboundary. Tensor contraction is natural under all coefficient maps; hence
the average and the corrected section define actual scheme morphisms.

The corrected section preserves products on affine points. Affine
extensionality on the universal pair extends that equality to every relative
scheme test. The resulting `extensionSection` is a group-scheme homomorphism;
`extensionSection_comp` proves that it splits the original quotient. The
proof uses no characteristic-zero or reductivity assumption and no Levi
decomposition result; the supplied invariant integral is the averaging input.
