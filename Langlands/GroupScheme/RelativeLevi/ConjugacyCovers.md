# Refining covers carrying all-test conjugators

This is internal derived content for relative Levi conjugacy.
The algebraic results concern arbitrary group-scheme homomorphisms and impose
no geometric Levi hypotheses.

`isRangeConjugator_baseChange_iff` identifies the all-test conjugator predicate
for two pulled-back homomorphisms with the original predicate for the projected
point. The actual pullback-point equivalence supplies the projection.
One direction applies the original predicate to the projected test scheme
and uses naturality and preservation of products and inverses.
For the other direction, every test scheme mapping to the projected domain
has an induced map to the new base. The identity of its underlying scheme
gives a relative isomorphism to the projected induced test scheme.
Range membership transports through that isomorphism. This accounts for all
test schemes, including nonreduced schemes.

`rangeConjugatorPointsEquiv` restricts the actual pullback-point equivalence
to the subtypes of points satisfying this predicate. Both inverse laws are
inherited from that equivalence.

`etaleLocallyRangeConjugate_of_baseChange` projects local conjugators over
the new base to the original base on the same cover. The structure maps of
each cover member differ only by association of composition; an identity
underlying relative map and restriction of the all-test predicate account
for that difference.

`etaleLocallyRangeConjugate_of_cover` flattens local existence over an
etale cover into local existence over the original test scheme. It chooses
the witnessing cover on each member and uses `ZeroHypercover.bind`, whose
members are indexed by pairs of outer and inner indices and whose maps are
the composite covering maps. Restriction along the identity underlying map
again reconciles the associated structure maps. The resulting cover index
universe is the maximum of the two original cover index universes.

These are categorical transport and cover-composition results. They assert
no geometric torus-existence or Levi-existence result and do not prove the
unchanged unconditional relative Levi conjugacy statement.
