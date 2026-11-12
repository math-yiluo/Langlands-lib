# The two-sided Hecke ideal of a central idempotent

This is derived infrastructure for Renard (9 July 2026), VI.7.4,
printed pp.185–186 / PDF pp.191–192. It imports the published
`Hecke.centralMultiplier` construction and its multiplier laws.

For a categorical central element on smooth complex representations with carrier
universe `max u v`, `centralIdeal` is the nonunital subring of actual Haar Hecke
elements fixed by its multiplier. The left and right multiplier laws show that it
is stable under multiplication on either side by arbitrary Hecke elements.
If the central element is idempotent, its multiplier is idempotent, so this
fixed set equals its image. `mem_centralIdeal_iff_regular` expresses this image
using the exact lifted left regular representation. Applying both multiplier
laws and idempotence shows multiplicativity, yielding the actual nonunital ring
retraction `centralIdealProjection` onto the ideal.

The assumptions are those of the underlying multiplier construction: a Hausdorff
locally compact nonarchimedean group with Borel measurable structure, a left Haar
measure and a smoothness witness for the left regular representation. No
Bernstein decomposition or existence of Bernstein projectors is proved here.
