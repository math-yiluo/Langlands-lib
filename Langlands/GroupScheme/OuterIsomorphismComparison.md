# Comparison of supplied outer-isomorphism quotients

Worker 635.

This is an internal categorical consequence of the supplied
`OuterIsomorphismScheme` laws. It works over every scheme and in every
universe, for two quotients of the same representing isomorphism scheme
and the same automorphic action. It has no reductivity or valuation
hypothesis.

`invariant_relation` proves that an invariant relative morphism is equal
on every pair of points with equal outer class. The orbit law supplies
an acting point on the same test, and invariance gives the equality.
`invariant_relation_left` equips arbitrary underlying test schemes with
their forced map to the base, so the same equality applies there.
`descend` uses effective descent of morphisms for the flat, surjective,
quasi-compact class map to produce an actual morphism over the base.
`classMap_descend` records its factorization. The effective epimorphism
also proves uniqueness, through `hom_ext` and `descend_unique`.

`comparisonIso` descends each quotient's class map through the other.
Both composites are identities by cancellation of the respective class
map. The two factorization equations and `comparisonIso_unique` state
that this is the unique isomorphism respecting the supplied class maps.

`FiniteGenericOuterClass.ofComparison` keeps the finite carrier and its
prescribed point and composes its class map with that comparison.
`nonempty_iff_comparison` makes finite-carrier existence independent of
the supplied quotient for this fixed representing scheme and action.
These constructions do not assert the existence, étaleness, or local
constancy of any outer quotient, or the existence of any finite carrier.
