# The diagonal pair action and the actual tuple threshold relation

This module specializes the generic diagonal action and quotient relation to
the tuple cross cover. It is internally derived infrastructure for the
symmetric-tuple filtration of Stacks Project, Lemma 68.8.6, Tag 07ST, and
Lemma 68.8.3, Tag 0BBN. The registered originals are
`stacks-noetherian-approximation-2026-11-01` and
`stacks-stratification-2026-11-02`. Those passages supply the tuple charts and
image filtration; the diagonal action and the quotient comparisons here follow
from the existing scheme constructions.

Work in arbitrary universe `u`, with an original relation `E` whose source is
separated, whose object and arrow schemes are affine, and whose joint endpoint
map is a closed immersion. Fix `p ≤ q`, write `L,H` for the two tuple tails,
`c : P → H.U` for the cross-cover source, and `v : P → L.U` for its target.
Write `A` for the higher-tail action on `P`, and `a,b` for the projections from
`P ×_{H.U} P`.

`tupleTailCrossCoverDiagonalAction` is the actual diagonal pair action
`A.pairAction`, over `a;c`. The endpoint lemmas
`tupleTailCrossCoverDiagonalAction_fst_target` and
`tupleTailCrossCoverDiagonalAction_snd_target` prove that this action preserves
both `a;v` and `b;v`. The generic diagonal-action projection formulas express
each projected action as an application of `A`; its target-invariance equation
then gives the asserted equality. This discharges the two explicit
compatibility premises of the earlier pair-kernel-pair module.

For `q < N+1`, `tupleTailCrossCoverDiagonalActionAffineQuotientCover`
applies that module's finite invariant affine quotient cover construction to
this action and these two proved equations.
`tupleTailThresholdDiagonalSchemeQuotient` similarly specializes the concrete
pair quotient to this action. Its quotient scheme is exactly the arrow scheme
of the chart relation on the `q`th threshold open `W` of `L.U`.

Let `Q` be the existing quotient of `A` with scheme `W`, and `Q₂` the quotient
just constructed. The generic relation `A.quotientRelation Q Q₂` therefore has
the same object and arrow schemes as `L.chart W.ι`.
`tupleTailThreshold_quotientRelation_s` and
`tupleTailThreshold_quotientRelation_t` identify their endpoint maps: the
quotient of pairs has source descended from `a` and target descended from `b`,
and the existing threshold pair-cover endpoint equations have precisely this
orientation. The characterizations of the descended maps prove both identities.
Finally, `tupleTailThreshold_quotientRelation_isCartesianHom` packages the
identity maps on the two schemes as a cartesian morphism. The square is
cartesian because both horizontal maps are isomorphisms.

This module constructs the compatible diagonal action and identifies its
actual threshold quotient relation. It does not yet produce a descended
finite-type system or a Noetherian first level.
