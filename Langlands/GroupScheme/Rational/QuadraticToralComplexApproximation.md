# Simultaneous approximation at complex places

A connected reductive group over a number field admits a dominant unirational
parametrization. The proof restricts its domain to a nonempty affine open of
affine space. Over each complex completion the image of the parametrization
contains the rational points of a nonempty Zariski open. Every nonempty analytic
open of the group meets this locus by normed-field Zariski density, and an
algebraically closed fibre supplies a rational parameter there.

The open immersion of the parameter domain into affine space carries the
neighborhoods of the chosen parameters to open sets of affine coordinates.
`InfiniteAdeleRing.denseRange_algebraMap` supplies one point over the number
field by weak approximation in these coordinates. Its membership in the
parameter domain can be tested after extension to any one of the complex
completions. Applying the parametrization gives the required group point.
If the field has no complex places, the identity supplies the point.
