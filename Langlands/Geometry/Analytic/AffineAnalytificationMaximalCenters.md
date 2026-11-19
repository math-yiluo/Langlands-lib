# Maximal centers of affine analytifications

`AffineAnalytification.maximalCenterLift` chooses an analytic point centered
at any maximal ideal of a finitely presented algebra. The complete,
ultrametric, nontrivially normed field and the algebra may have independent
universes.

The finite polynomial presentation gives finite type. The maximal-ideal
quotient is a field and Zariski's lemma gives its finiteness over the ground
field. Its spectral norm is a multiplicative norm extending the ground-field
norm. Pulling this norm back gives a seminorm with zero ideal equal to the
specified maximal ideal. The published range theorem for `pointSeminorm`
realizes that seminorm by an analytic point.

For a flat algebra map whose analytification is surjective on points, each
chosen point over a maximal ideal lifts along the analytified map. Center
naturality gives a prime ideal in the receiving algebra that contracts to the
maximal ideal. Thus the extension of each maximal ideal is proper. The
faithful flatness criterion gives an injective ring map, so a surjective
algebra map satisfying these hypotheses is bijective.

These are internal consequences of the Library's affine seminorm range and
center comparison, combined with the spectral norm and faithful flatness
results in Mathlib. The quotient criterion applies to the comparison between
two closed affine overlaps in the algebraic-space immersion problem.
