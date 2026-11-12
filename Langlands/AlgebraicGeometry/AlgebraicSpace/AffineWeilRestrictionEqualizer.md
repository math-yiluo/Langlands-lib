# Equality loci over arbitrary affine Weil test schemes

Authors: Worker 160 and Worker 117.

This is an internal assembly for Task 5360. Worker 160 authored the
full-slice comparisons and this affine-coordinate assembly; Worker 117
supplied the diagonal geometry, quasi-affine equality loci and
closed-immersion preservation helpers used here. These are deductions
from the named Library and supporting interfaces rather than a new
translation of an external source assertion.

`representedBaseIso` transports any full presheaf representation across
an isomorphism `e : U ≅ T` of base schemes. A scheme `W` over `U`
represents restriction of the presheaf along `e.hom`; the pullback of
`W` along `e.inv` then represents the original presheaf over `T`.
The proof uses `representedBaseChangeIso` and identifies the composite
slice functor with the identity by `Over.mapComp`, `Over.mapCongr`
and `Over.mapId`. No sheaf assumption or geometry is needed for this
categorical construction.

`exists_affineTest_sectionEqualizer_weil` takes arbitrary commutative
rings `R`, `R'`, a finite projective `R`-algebra structure on `R'`, a
quasi-separated algebraic space `X'` over `Spec R'`, an arbitrary affine
test scheme `T` over `Spec R`, and two sections of the full restricted
presheaf over `T`. It constructs one scheme `W` over `T.left` with:

- a full natural representation of `sectionEqualizer x y`;
- a quasi-compact structure map;
- a closed structure map if `X'` is separated.

The proof chooses `A = AffineCoordinateRing R T` and
`B = A ⊗[R] R'`. The existing affine presentation
`affineSchemeOverIso R T` identifies the specified `T` over `Spec R`
with `Spec A`. The canonical tensor square is cartesian by
`isPullback_weilRestrictionTensor`; its finite projective
`A`-algebra structure uses Mathlib's tensor-product module instances.
The two sections are transported to that affine lower test and then
to the specified upper test `Spec B`.

`exists_quasiAffine_representsEqualizer` supplies a monomorphic,
locally finite type, quasi-compact, quasi-affine upper equality locus
`Y`. Viewing its projection as a scheme over `Spec B`, its actual
`affineChartWeilRestriction A B Y` represents the lower equality
presheaf by `sectionEqualizerWeilRepresentationIso`.
Its structure map is quasi-compact by
`quasiAffineWeilRestriction_schemeProperties`.

`sectionEqualizerRestrictIso` expresses that representation as the
restriction of the original equality presheaf. `representedBaseIso`
then transports it back to a scheme over the original `T.left`.
The final representative is an actual scheme pullback, so its
quasi-compactness follows by base change.

If `X'` is separated, `property_of_mono_representsEqualizer` gives
closedness of this same upper equality locus. The helper
`quasiAffineWeilRestriction_hom_isClosedImmersion` gives a closed
structure map on its actual Weil scheme. Closedness is then preserved
by the final scheme base change. Thus the optional closedness claim
concerns the same representative as the quasi-compactness claim.

All scheme tests and the universe parameter are retained. Neither the
original algebraic space nor the affine test scheme is assumed to be
of finite type over the original base ring. This module does not use
or prove the algebraic-space Weil representability theorem and does
not glue over nonaffine test bases; the latter is the remaining
assembly step.
