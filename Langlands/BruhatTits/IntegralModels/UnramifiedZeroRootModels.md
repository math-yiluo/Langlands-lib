# Root models in a characterized unramified zero-fixer model

This internal construction combines the published integral-root construction
with the published root intersection for an arbitrary unramified zero datum.
It applies to a smooth affine model `N` over the maximal unramified integers
whose actual integral points are
`E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' Ω)`.
An actual compatible integral split torus `A : IntegralSplitTorusData N C.i`
is a supplied input.

For a nonempty apartment subset `Ω` bounded above under every affine real
functional, a reference point `x`, and an actual relative root `a`,
`unramifiedZeroRootFiltrationModelData` constructs a
`RootFiltrationModelData` at depth `C.apartment.rootFixerDepth a x Ω`.
Its generic group and inclusion represent the full generic root functor.
Its integral model is smooth, affine, and has geometrically connected fibres.
The map `unramifiedZeroRootFiltrationModelMap` is its actual compatible
closed inclusion into `N`; it also represents the full integral root functor
for `A.integralCharacter a`.

The exact point image is proved, rather than supplied as a separate premise.
`IntegralSplitTorusData.rootModel_integralPoints_eq` identifies that image
with the intersection of `N.integralPoints` and the root subgroup points.
The zero-fixer characterization and
`rootGroupPoints_inf_unramifiedZeroFixer_eq_rootFixer` identify this
intersection with the root fixer of `Ω`.
`rootFixer_eq_filtration_of_bounded` then identifies the fixer with the
specified filtration level. The geometric properties and the compatible
closed inclusion come from the existing `IntegralModel.SplitRoot`
construction.

The general helper `rootModelMap_isRepresentedBy` exposes the all-test
integral-root representation already proved by
`IntegralModel.SplitRoot.integral_properties`. The specialized
`unramifiedZeroRootFiltrationModelMap_isRepresentedBy` retains that property
for the filtration-model package.

This construction uses the neutral-model characterization occurring in the
descended facet problems directly. It requires neither a supplied full
one-fixer model nor a characterization of such a full model. It does retain
the supplied compatible integral apartment torus. It proves no existence
of that torus, no residue-root or radical-kernel formula, and no facet
Lie-weight sign formula.
