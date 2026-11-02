# Invariant completed ranges of actual automorphic tensor slices

This internal construction uses the genuine finite tensor presentation `P`,
supplied global invariant positive form `b`, and independently quantified
number-field and local-carrier universes of `FiniteTensorHilbertCovariance`.

`sliceHilbertRange` is the actual range of `sliceHilbertIntertwiner`, hence a
subrepresentation of the original `b.completedRepresentation` restricted along
the actual `localInclusion`. The underlying complex submodule is definitionally
`sliceHilbertSubspace`, because the completed intertwiner's underlying linear
map is exactly `sliceHilbertEmbedding.toLinearMap`. There is no nonzero-tail
hypothesis, so zero tails and zero slices are included.

`coe_sliceHilbertRange` identifies its set with the exact slice-embedding image.
`completedOperator_mem_sliceHilbertRange` exposes the inherited invariance using
the original global completed operator at each actual local insertion.
Closedness and the closure formula for the original embedded slice reuse the
existing `FiniteTensorHilbertRange` laws on the unchanged underlying submodule.

For an explicitly nonzero complementary tensor, the factor embedding has
exactly this invariant range. Combining that equality with the existing
factor-image closure law identifies this same range with the closure of
`x ↦ b.toHilbert (P.localEquiv v (x ⊗ₜ[ℂ] y))`, for `x : V v`. These two laws
retain the nonzero-tail hypothesis of the factor-to-slice equivalence.

This range is built from the specified actual completed map. Existence of a
tensor presentation or positive form, a general Hilbert tensor decomposition,
canonical local normalization, spectral occurrence and archimedean globalization
are not asserted. Invariance concerns the inserted local subgroup; the range
need not be invariant under every global element.
