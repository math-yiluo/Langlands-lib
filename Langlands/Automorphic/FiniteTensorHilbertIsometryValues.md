# Continuous inverse maps and values of tensor range isometries

This internal construction first develops evaluation laws for
`TensorRepresentationIsometryAux.rangeRepresentationIsometry` on independently
quantified complex normed carriers. Forgetting the inherited range subtype
recovers the original intertwiner. Applying the inverse gives a source vector
whose intertwiner value is the prescribed ambient range value. The same two
laws hold after composition with a preceding complex-linear isometric
equivalence, with an independently quantified source carrier. The
representations need only be algebraic representations of a monoid; norm
preservation of the supplied intertwiner is an explicit hypothesis.

The generic forward identities follow from the existing definitions. The
inverse identities follow by applying the ambient subtype projection to the
inverse identities of the isometric equivalence. The final identity combines
the forward identity for a composite with its right inverse identity.

For a genuine finite tensor presentation and supplied invariant positive form,
`FiniteTensorPresentation.sliceHilbertInverse` constructs the continuous
complex-linear inverse from the inherited actual invariant slice range to the
slice-form Hilbert completion. It forgets only the isometric structure of the
inverse of `sliceHilbertRepresentationIsometry`. Zero tails and zero slices
remain allowed. For an explicitly nonzero complementary tensor,
`factorHilbertInverse` likewise constructs the continuous complex-linear
inverse from the same range to the factor-form Hilbert completion, using
`factorHilbertRepresentationIsometry`. Both maps have norm-preserving inverses
by those existing isometric equivalences; continuity and linearity are retained
by Mathlib's forgetful maps. The field and local carriers have independent
universes, and the rank is any natural number. The domain retains the inherited
norm and the original global completed action restricted at the local insertion.

These inverse maps are obtained from the already constructed equivalences,
without an additional inverse, surjectivity or compatibility premise. This
unit exports the generic evaluation identities and the actual continuous
inverse constructors. No additional actual slice or factor evaluation
comparison theorem is asserted here. No existence of a presentation or form,
canonical normalization, spectral occurrence, invariance under the entire
global group or archimedean globalization is asserted.
