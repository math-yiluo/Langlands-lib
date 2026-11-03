# Affine neighbourhoods of finite sets on ample schemes

`AmpleFiniteAffineOpenStatement` asserts that, for every universe and
scheme `X`, an actual ample line bundle `L` has the following consequence.
For any open `W` and finite set `E` of points contained in `W`, there is
an affine open `U` of `X` containing `E` and contained in `W`. There is no
separatedness, noetherianity, field or nonemptiness hypothesis. In
particular, the empty finite set is included.

This is an internal derived interface for the finite-set part of
`ProperFibreAmpleAffineOpenStatement`. Its provenance is the Library's
actual ampleness predicate and the published results named below. The
supporting lemmas implement the generic geometric argument in the same
file. Submission as a statement provides no exact-target proof receipt
for the proper-family proposition.

The implemented argument first proves
`LineBundle.IsAmple.pullback_of_isAffineHom`: affine pullback preserves
the actual ampleness predicate. An affine morphism is quasi-compact, so
its source is compact when its target is compact; the affine section
loci in the target pull back to affine loci of the pulled-back sections.

`isAffineHom_trivializationInclusion` proves that the inclusion of a
line-bundle section locus is affine. Its intersection with every affine
open is affine by the published `affineGenerationLocusIntersection`.
The identification uses the canonical open immersion and its image.

`LineBundle.IsAmple.quasiAffine_sectionOpen` applies this to a section
of a positive tensor power of an ample bundle. The tensor power remains
ample by `positiveTensorPowerAmple`, its restriction to the section open
is ample by affine pullback, and the section trivializes that restriction.
The published `ampleTrivialQuasiAffine` then makes the section open
quasi-affine.

`exists_isAffineOpen_of_finite_of_quasiAffine` embeds a quasi-affine
scheme into the spectrum of its global functions. The published
`GenericPointAvoidance.exists_basicOpen_of_finite` places the finite
image inside one basic open contained in the image of this open immersion.
The inverse image is affine and contains the original finite set.

Finally, `exists_isAffineOpen_of_finite_of_ample` uses the published
`ampleFiniteSetSection` to put `E` in a positive-power section open `T`
inside `W`. The inverse image of `E` in `T` is finite because the open
inclusion is injective. The preceding quasi-affine argument gives an
affine neighbourhood there, and its image under `T.ι` is an affine open
of `X` contained in `W`. This proves the conclusion expressed by the
new interface, with the same quantifiers and hypotheses.

Fibre-ampleness spreading remains a separate prerequisite. This file
supplies the generic ample-scheme argument; obtaining ampleness on a
neighbourhood of a proper fibre and transporting the finite set from
that family remain obligations of the host proper-family proof.
