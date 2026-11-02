# Extending actual curve places

This derived construction extends an actual discrete curve place of `K` over `k`
to a finite extension `F / K`, with the given compatible constant-field algebra
structures. The three fields can have independent universe levels. No
separability or perfectness hypothesis is imposed.

`curvePlaceExtension` chooses the DVR supplied by the published theorem
`ValuationSubring.exists_isDiscreteValuationRing_dominates_of_finiteDimensional`.
It contains the image of the original valuation ring and takes its maximal ideal
into the nonunits of the chosen ring. Constants remain integral by the scalar
tower law. A DVR cannot be the top valuation subring, since that subring is
isomorphic to the ambient field. The DVR's principal ideal property therefore
packages this valuation ring as an actual `AlgebraicCurve.Place k F`.

The membership and dominance lemmas expose the supplied properties.
`curvePlaceExtension_mem_iff` proves exact restriction: if a field element is
outside the original ring, its inverse is a nonunit there; dominance makes its
image a nonunit upstairs, so the original element's image cannot be integral.
`curvePlaceExtension_comap` expresses this as equality of literal valuation
subrings under pullback.

For any finite extension of `RatFunc k`, `curvePlaceReference` applies this
construction to the rational-function place at zero.
`curvePlace_nonempty` records the resulting inhabitant. This works over any
constant field with the specified compatible rational-function presentation.

The published extension theorem comes from the registered Anthropic FLT source
at commit `6e837e75355538c7f80bab5b956861e86c4eacc2`, literature id
`anthropic-flt-complete-lean-source-6e837e75`. This module imports the published
theorem by Lean name and copies none of its proof.

Conrad, *Weil and Grothendieck approaches to adelic points* (December 31, 2011),
printed p.1, uses finite nonempty sets of places for adelic levels. The present
nonemptiness construction is derived infrastructure for that convention. It
does not identify these actual curve places with a separate conventional
global-place type or prove any geometric point-space comparison.
