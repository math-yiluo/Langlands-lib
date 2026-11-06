# Proper two-block parabolics and their canonical radical images

This internal construction uses the existing consecutive two-block weight:
weight one on the first block of size `a` and weight zero on the second block
of size `b`, with `a + b = n`. Both block sizes must be positive.

`twoBlockParabolic_ne_top` works over any nontrivial commutative ring `R`.
It proves that the existing all-test block parabolic subgroup functor is
different from the whole group functor. On the identity test scheme over
`Spec R`, the proof constructs the invertible lower block matrix
`[[1, 0], [X, 1]]`, with every entry of `X` equal to one. Its inverse has
lower block `-X`. The entry from the second block to the first is one,
whereas membership in the block parabolic would force it to be zero.
The global-section ring of this test is nontrivial by `ΓSpecIso`.

For a field `F` of arbitrary universe,
`generalLinearTwoBlockProperParabolic` packages the existing dynamic parabolic
of this diagonal cocharacter as an actual proper rational parabolic.
Geometric connected reductivity of `GL_n` is supplied by
`isConnectedReductive_generalLinear`. Geometric parabolicity retains the
explicit universal premise `ParabolicDynamicStatement`; no proof of that
premise is claimed. The displayed value theorem identifies this parabolic
with the existing block parabolic on every test scheme.

`properRationalParabolicRadicals_generalLinearTwoBlock` proves that its
canonical ambient radical image is the existing two-block unipotent subgroup
functor, on every test scheme. It accepts any proof of geometric connected
reductivity of this same `GL_n`, so it applies directly to the intrinsic
all-proper-parabolic family. The proof composes
`rationalParabolicRadical_eq_dynamic` with
`unipotent_diagonalCocharacter`.

The provenance is entirely internal: the explicit matrix argument and the
published dynamic block comparisons supply properness and the value
identities, and the canonical dynamic-radical bridge supplies the radical
identity. This module constructs a member of the intrinsic indexing family.
It makes no claim of parabolic classification, adelic measure comparison,
cuspidal equivalence, reduction theory or finite volume.
