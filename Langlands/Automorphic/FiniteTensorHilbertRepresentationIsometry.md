# Isometric realizations of actual tensor representation equivalences

This internal construction uses the genuine finite tensor presentation, supplied
global invariant positive form and independently quantified field and local
carrier universes of `FiniteTensorHilbertRepresentationEquiv`, for every natural
matrix rank.

The general helper `TensorRepresentationIsometryAux.norm_rangeEquiv` proves
that the published injective-intertwiner range representation equivalence
preserves a supplied norm equality of the original intertwiner. Its range has
the inherited ambient norm, and its forward map is the original intertwiner,
so that same equality proves the result. `isometryOfNorm` supplies an existing
complex-linear equivalence with a proved norm equality as a complex-linear
isometric equivalence. `rangeRepresentationIsometry` combines these two helpers
on the abstract normed carriers, upgrading the existing range representation
equivalence to an isometric equivalence with its identical underlying linear
equivalence. The group and the two normed carriers have independent universes;
action operators need not be assumed continuous or isometric.

`sliceHilbertRepresentationIsometry` applies these helpers to the actual
completed slice intertwiner and the norm equality of the actual slice Hilbert
embedding. Its target is the inherited norm on the whole actual invariant
slice of the original completed global representation restricted along the
genuine local insertion. The underlying linear equivalence is exactly that
of `sliceHilbertRepresentationEquiv` by construction. The construction
permits zero tails and zero slices.

For an explicitly nonzero complementary tensor,
`factorHilbertRepresentationIsometry` composes the actual factor-to-slice
Hilbert equivalence with the slice representation isometry. Its underlying
linear equivalence is exactly that of `factorHilbertRepresentationEquiv`
by the definitions of both compositions. The range
retains its inherited original-global-completion norm and action. Thus the
isometric and representation interfaces refer to the same linear maps.

The unit derives these structures from the published generic range equivalence
and the actual tensor completion maps; it makes no new literature
identification. No presentation, positive form, nonzero tail, general tensor
decomposition, canonical normalization or spectral occurrence is asserted to
exist. Invariance concerns the inserted local subgroup. Archimedean
globalization remains separate work.
