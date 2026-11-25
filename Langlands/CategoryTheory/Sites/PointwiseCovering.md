# Covering points from pointwise lifting squares

This is an internal categorical reduction for sites defined by jointly
surjective families. Let `C` be a category and `F : C ⥤ Type w` a functor
giving the points of its objects. No faithfulness or preservation of limits
is assumed.

`HasPointwiseLiftingSquares F` requires the following property. For any
cospan `f : X ⟶ S`, `g : Y ⟶ S` and points `x` and `y` having the same
image in `F.obj S`, there are an object `T`, arrows `p : T ⟶ X` and
`q : T ⟶ Y`, and a point `t` of `T` such that `p ≫ f = q ≫ g`,
`F.map p t = x`, and `F.map q t = y`. The square may depend on both points
and is not required to have a universal property.

`IsJointlySurjective F S` says that every point of the target of the sieve
`S` is in the image of an arrow in `S`. This is the sieve version of the
existing Mathlib jointly surjective precoverage after comapping along `F`.

## Implemented argument

The top sieve is jointly surjective using the identity arrow. Under
`HasPointwiseLiftingSquares`, joint surjectivity is stable under pullback
of sieves: lift the chosen point of a covering arrow and the given point
of the new target to a commuting square. Closure of the original sieve
under precomposition puts the second leg in its pullback sieve.

Joint surjectivity also satisfies transitivity without any lifting
hypothesis. First lift a target point along an arrow of the outer sieve,
then along an arrow of the appropriate pullback sieve, and compose the
two arrows. The functor's composition law gives the required point image.
These constructions define `jointlySurjectiveTopology F hF`.

`isJointlySurjective_of_mem_toGrothendieck` proves, by induction on the
generated topology, that every covering sieve for
`(Types.jointlySurjectivePrecoverage.comap F).toGrothendieck` is jointly
surjective under the explicit lifting hypothesis. The generator case
uses Mathlib's description of the comapped precoverage and the inclusion
of a presieve in its generated sieve. The other cases are precisely the
top, pullback, and transitivity arguments above.

`mem_toGrothendieck_iff` includes the converse: a jointly surjective sieve
is already a covering presieve, hence its generated sieve is covering.
`toGrothendieck_eq_jointlySurjectiveTopology` identifies the resulting
topologies.

## Provenance and scope

All constructions and proofs are derived from Mathlib's `Sieve`,
`Types.jointlySurjectivePrecoverage`, and `Precoverage.Saturate`. They
introduce no external literature assertion and require no categorical
pullback objects or base-change instances.

For the analytic étale site, the intended functor is `EtaleSite.points X`.
The lifting hypothesis then remains an actual geometric obligation:
the lifting object must itself be an étale object over `X`, the square
must commute as morphisms of that site, and its point must have both
prescribed projections. This module does not establish that obligation,
the unconditional analytic covering-points statement, analytic finite
subcovers, or the cohomology comparison.
