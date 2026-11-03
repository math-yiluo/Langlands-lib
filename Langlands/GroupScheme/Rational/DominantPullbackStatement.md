# Dominant affine maps and actual coordinate injectivity

`PointedCoordinateWeights.DominantPullbackStatement` is a proposition
uniform in every universe `u`, field `k`, and morphism `f : V → W` of
affine schemes over `k`. It asserts that topological dominance of `f`
and reducedness of `W` imply injectivity of the actual affine-coordinate
pullback constructed in `PointedCoordinateAction`. No action, rational
point, smoothness, splitness, or characteristic assumption is needed.

This is a derived geometric source target for the use of dominant
pullback in Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition
(2015), §3.3, printed pp.107–108 (PDF pp.133–134), registered source
`conrad-gabber-prasad-2015-pseudo-reductive`. Their pointed affine
varieties are geometrically integral, so satisfy the retained reducedness
hypothesis. Reducedness is necessary in this general formulation because
topological dominance alone does not detect nilpotents in the target.
The construction uses the given affine schemes and their chosen actual
coordinate presentations; it does not replace the map by an unrelated
linear injection.

This file defines the target and does not prove it. Together with the
proved `support_subset_of_injective`, it gives the support containment
needed for dominant pointed equivariant maps. A focused proof successor
must connect topological dominance over a reduced target to injectivity
of this precise coordinate pullback, for example through scheme-theoretic
dominance and the affine coordinate isomorphisms.
