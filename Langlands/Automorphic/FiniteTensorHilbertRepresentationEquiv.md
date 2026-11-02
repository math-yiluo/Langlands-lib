# Representation equivalences onto actual invariant tensor slices

This internal construction uses the same genuine finite tensor presentation
and supplied global invariant positive form as `FiniteTensorHilbertInvariantRange`.
Independent number-field and local-carrier universes and every natural rank
are retained.

`sliceHilbertRepresentationEquiv` applies the published generic
`Langlands.Classification.JuxtaposedShuffle.rangeEquivOfInjective` to the actual
completed slice intertwiner and injectivity of its underlying linear isometry.
Its target is the inherited representation on the actual invariant slice range
of the original global completed action restricted along the genuine local
insertion. It permits zero tails and zero slices.

`factorSliceHilbertRepresentationEquiv` packages the existing actual completed
factor-to-slice Hilbert equivalence as a representation equivalence, using its
proved completed-operator covariance. For an explicitly nonzero complementary
tensor, `factorHilbertRepresentationEquiv` composes it with the slice range
representation equivalence. Its target is the inherited representation on the
whole actual invariant slice in the unchanged original global completion.

This is an internal reuse of the existing injective-intertwiner range theorem
and actual tensor completion maps, without a new literature identification.
No positive form, presentation or nonzero tail is asserted to exist. The range
action concerns the inserted local subgroup. General Hilbert tensor
decomposition, canonical normalization, spectral occurrence and archimedean
globalization remain separate work.
