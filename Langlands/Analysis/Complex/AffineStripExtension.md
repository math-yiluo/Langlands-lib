# Holomorphic limits from affine spectral strips

`AffineStripExtensionStatement` considers a sequence of entire functions
of an adjoining parameter and a spectral variable. The sequence has
exponential strip growth on slices with the adjoining parameter fixed
and on slices of the form `s ↦ (v + s, s)`. For bounded `|Re v|`, its
differences are exponentially weighted Cauchy on pairs of vertical
boundary lines of the latter slices. The conclusion gives a locally
uniform limit, holomorphic after every holomorphic complex curve, and
exponential strip growth at each fixed adjoining parameter.

The proof applies the vertical-strip estimate separately on each affine
slice. The factor depending on `|Im v|` is part of the boundary constant
on that slice. For a point `(u, s)`, the slice through it has `v = u − s`.
On bounded subsets of the two variables this bounds the differences
uniformly. Completeness of `ℂ` gives the pointwise limits and the same
bounds give locally uniform convergence. Restriction by a holomorphic
curve and the one-variable uniform limit theorem give holomorphy along
that curve.

On a vertical spectral strip with `u` fixed, `|Re (u − s)|` stays bounded
and `|Im (u − s)| ≤ |Im u| + |Im s|`. The estimate of the difference from
one fixed approximant and that approximant's strip growth give the
asserted strip growth of the limit.

This is an internal tool for approximating the square tests in Jacquet,
*Archimedean Rankin–Selberg integrals* (2009), §8.2, pp. 54–58. In the
application the adjoining exponents lie in opposite absolute convergence
regions on the two boundary lines.
