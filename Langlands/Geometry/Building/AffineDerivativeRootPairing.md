# Rational root systems from all affine derivatives

This module extends the published full derivative pairing in
`SpecialPointExistence`. For any `IsAffineRootSystemWithRankZero Ψ`, it constructs
a finite crystallographic rational root system on the rational span of every
derivative root. The translation space and affine space have independent
universes. The empty, rank-zero system is permitted.

The root indices are exactly `derivativeRoots Ψ`. No choice of a reduced
subsystem is made. In particular, the construction does not assert reducedness
or symmetry of its root-coroot pairings.

The existing real derivative pairing has full root span by AR 1. Mathlib's
`RootPairing.rootSpan_eq_top_iff` gives full coroot span from finiteness and
crystallographic integrality, proving `derivativePairing_isRootSystem`.
`RootPairing.restrictScalars ℚ` then restricts the pairing to the rational spans
of all roots and coroots.

The new `rationalDerivativePairing` transports the coroot space along the perfect
pairing isomorphism into the dual of the rational root space. Roots remain fixed.
The inverse isomorphism identity proves that its bilinear map is exactly
`Module.Dual.eval`. The root-image theorem identifies its full image in the real
dual translation space with `derivativeRoots Ψ`. Its rational root-coroot
pairings, cast to the reals, are exactly
`a.val (hΨ.derivativeCoroot b)`. Injectivity of the rational-to-real scalar map
therefore proves crystallographic integrality and the stated equivalence of
pairing symmetry.

This is an internal derived construction using the published affine-root-system
axioms, the published `derivativePairing`, and the named Mathlib restriction and
perfect-pairing results. It supports a later comparison with the rational span
of actual relative roots. That comparison, full-root reducedness, pairing
symmetry, group splitting and the anisotropic affine-diagram target remain
separate obligations.
