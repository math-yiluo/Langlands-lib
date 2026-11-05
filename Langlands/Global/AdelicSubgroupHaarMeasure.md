# Intrinsic Haar measures on actual adelic subgroup rational quotients

This internal measure adapter works on the actual evaluated subgroup of
an affine group scheme of locally finite type over any number field.
The subgroup functor is arbitrary. Its actual principal image is
discrete because it is contained in the inverse image, under subgroup
inclusion, of the ambient discrete principal subgroup. This argument
does not identify that inverse image with the subgroup's rational image,
or assert rational descent for an arbitrary functor.

When an actual closed group-scheme embedding represents the functor, the
adelic subgroup is closed by the published closed-immersion theorem on
actual affine points. Given this proved or supplied closedness, its
subspace topology is locally compact and Polish, and its rational
quotient's inherited measurable structure is Borel.

`rationalQuotientHaarMeasure` applies the existing discrete left quotient
construction to Haar on this actual subgroup, with counting measure on
its actual principal image. It is nonzero, locally finite and regular.
No represented source is chosen for the measure, and no transport through
a surjection selects its normalization.

If the actual rational quotient is compact, local finiteness makes the
total mass finite, and nonzeroness makes it positive. The module scales
both the actual subgroup Haar measure and its quotient by the inverse of
that same mass. `normalizedRationalQuotientHaarMeasure` is then a
probability measure; `normalizedHaarMeasure` is the corresponding
positive finite scalar multiple of ambient subgroup Haar.

With the explicit analytic right-invariance hypothesis on that subgroup
Haar measure, positive quotient right translations preserve the
normalized measure. The normalized ambient and quotient measures satisfy
the original exact counting-measure complex Weil compatibility. The
proof scales the existing compatibility: nonzeroness comes from
probability mass one, regularity and integrability are preserved under
finite scaling, and both sides of the integral identity acquire the
same real scalar.

This construction uses `AdelicSubgroupQuotient`, `AdelicGroupHaarMeasure`,
`AffinePointClosedImmersion`, `LeftCosetHaarMeasure`,
`LeftCosetWeilMeasure` and pinned Mathlib measure scaling. It does not
assume that an algebraic adjoint determinant is an analytic modulus,
prove subgroup unimodularity, or prove compactness for an arbitrary
subgroup. The parabolic-radical compactness application belongs to the
separate canonical-family consumer.
