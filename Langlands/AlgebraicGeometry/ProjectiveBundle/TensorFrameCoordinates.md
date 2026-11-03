# Coordinates of tensor frames

This derived unit transports the comparison of line trivializations to genuine
frame coordinates on the original base opens. `TensorFrames.trivializationUnit`
is the unit comparing two trivializations of the restricted line module,
transported through `U.topIso` to the ring of functions on `U` in the base scheme.
Its value is the published `SchemeModule.SectionClearing.chartCoeff` of the composite from the
first trivialization to the second. Its identity, inverse, and composition laws
come from the corresponding laws for `tensorTrivializationScalar`.

`contraction_change` specializes the published `modE_mul` to the identity of the
tensor product module and to the contraction comparison. On every smaller
original open, the two contraction maps differ by the restriction of this unit.
The companion restriction-frame coordinate formulas identify actual tensor-frame
coordinates with contraction followed by the original frame coordinates.
Linearity then gives the coordinate comparison under a change of line
trivialization.

For two frames on the same trivializing open, the actual dual-frame transition
coefficients equal the original dual-frame coefficients multiplied by the
comparing unit in the reverse order. The proof uses the published formula for
dual-frame coefficients, the tensor-coordinate comparison, and cancellation
of contraction against expansion in the same trivialization.

No local-freeness or finite generation hypothesis is added: the supplied genuine
frames and trivializations are all that these local formulas use. Compatibility
between different trivializing opens, global tensor-line projective invariance,
and the host `LargeLevelRepresentabilityStatement` remain separate obligations.
