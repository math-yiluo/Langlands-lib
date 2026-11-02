# Hilbert equivalences onto actual invariant tensor slices

This internal construction uses a supplied genuine finite tensor presentation
`P`, global invariant positive form `b`, and independent number-field and
local-carrier universes, for every natural matrix rank. Its input data and
ambient completion are those of `FiniteTensorHilbertInvariantRange`.

`completeSpace_sliceHilbertRange` uses the proved closedness of the actual slice
in the complete original global completion to provide completeness for its
inherited metric. The submodule already inherits its norm and inner product
from this global completion.

`sliceHilbertRangeEquiv` applies Mathlib's `LinearIsometry.equivRange` to the
actual `sliceHilbertEmbedding`. Its target is the range of that embedding as a
complex submodule. This is definitionally the underlying submodule of the
existing `sliceHilbertRange`, since that invariant range is the range of the
intertwiner with exactly the same underlying linear map. The result is a
complex-linear isometric equivalence from the slice-form Hilbert completion
onto this whole closed slice, with the inherited norm. Its ambient forward map
is the slice embedding by the definition of Mathlib's range equivalence. The
construction includes zero tails and zero slices.

For an explicitly nonzero complementary tensor, `factorHilbertRangeEquiv`
composes the actual `factorSliceHilbertEquiv` with this slice range equivalence.
It is a complex-linear isometric equivalence from the specified factor-form
Hilbert completion onto the same actual closed invariant slice. Its ambient
forward map is the factor Hilbert embedding by the definitions of composition
and the range equivalence. Its inverse comes from the existing equivalences;
no inverse or surjectivity witness is supplied as additional input.

The construction specializes Mathlib's range equivalence and composes it with
the previously constructed actual factor-to-slice equivalence. This is internal
provenance and makes no new literature identification. No positive form,
presentation or nonzero tail is asserted to exist. The unit constructs the
isometric equivalences and target completeness; representation-equivalence
packaging, a general Hilbert tensor decomposition, canonical normalization,
spectral occurrence and archimedean globalization remain separate work. The
range is invariant under the inserted local subgroup, as in the imported unit.
