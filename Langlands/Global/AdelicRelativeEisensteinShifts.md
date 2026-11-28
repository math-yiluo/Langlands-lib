# Shift equations for relative Eisenstein series

`relativeEisensteinSeries` is the sum over the rational cosets of
a smaller parabolic inside its containing parabolic. If the
summand is invariant under the adelic radical and rational Levi of
the smaller parabolic, each rational representative can be
replaced in the evaluation by a rational point of the containing
Levi. That Levi commutes with its positive split component.
The shift also preserves the original invariance, so the
replacement works for both the original and shifted arguments.

Thus relative summation commutes with each positive split shift
and preserves absolute summability under these shifts. Linearity
on the submodule of invariant functions with summable series
extends the commutation to the full group algebra.
`relativeEisensteinSeries_shift` applies this to an exponent
polynomial of the summand. The corresponding raw root is its
exponent evaluated at the lift of the outer positive point.
`relativeEisensteinSeries_shift_finsetSum` uses one factor per
exponent in a finite decomposition. The product annihilates the
sum before relative summation, so that argument only requires
summability of the full integrand.

The mathematical setting is the restriction of exponents of the
relative summands in E. Lapid, *On the asymptotic inner product
formula for Eisenstein series*, pp. 321–323, (12)–(13), as used
in P. Delorme, *On the spectral theorem of Langlands*,
Advances in Mathematics 426 (2023), 109107, pp. 16–17,
(4.2)–(4.4).
