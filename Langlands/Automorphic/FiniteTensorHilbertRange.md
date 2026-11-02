# Closed Hilbert subspaces of actual automorphic tensor slices

This internal continuation uses the actual `FiniteTensorHilbertEmbedding`
constructors and their exact original-vector formulas. Inputs remain the genuine
finite automorphic tensor presentation `P`, a supplied invariant positive form
`b` on its actual global image, all natural matrix ranks, and independent
number-field and local-carrier universes. No positive form or tensor presentation
is asserted to exist in general.

`sliceHilbertSubspace` is the actual complex-linear range of the constructed
slice Hilbert isometry inside the same `b.HilbertCompletion`. It requires no
nonzero-tail hypothesis. Its underlying set is exactly that range, is closed,
and equals the closure of the embedded original slice
`{b.toHilbert (P.sliceInclusion v y f) | f ∈ (P.slice v y).Space}`.

For a specified nonzero complementary tensor and its explicit proof `hy`, the
actual `factorHilbertEmbedding` has this entire completed slice as its range.
Its range is also exactly the closure of the original pure-tensor images
`b.toHilbert (P.localEquiv v (x ⊗ y))`. This is equality of actual subsets of the
global completion, rather than an identification with a new abstract Hilbert
model.

Closedness follows from completeness and the existing linear isometry.
The original-slice closure identity specializes the published generic
`coe_completedRange_eq_closure`. The factor-to-slice equivalence is surjective,
so its composite with the slice embedding has the same range. The pure-tensor
closure identity is proved directly by density of the factor's canonical
embedding and the exact original-vector formula; the reverse inclusion uses
closedness of the isometric image.

Provenance is internal composition of the actual presentation and extracted
forms in `FiniteTensorUnitaryForm`, the constructions and evaluation laws in
`FiniteTensorHilbertEmbedding`, and the generic completion laws in
`Representation/Unitary/CompletionIntertwiner` and `CompletionTransport`.
No original-literature identification is added. Covariance under the actual
locally inserted action remains separate work. No general Hilbert tensor
product decomposition, canonical local form, spectral occurrence, full
archimedean globalization or smooth-vector recovery is claimed.
