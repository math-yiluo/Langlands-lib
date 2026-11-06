# Recovering actual base-change isomorphisms

Author: Worker 1442.

This internal construction recovers an actual isomorphism of base-changed group
schemes from a natural `LocalGroupIso` family. It uses the existing pullback
point equivalence and the fully faithful group-valued Yoneda embedding.
No structural theorem about algebraic groups is used.

A test scheme over `U` has a canonical point of `U` when viewed over the
original base. `baseChangeTestPoint` is this point, and
`map_comp_baseChangeTestPoint` expresses its compatibility with all maps of
tests over `U`.

For each such test, `baseChangePoints` projects a point of the pullback of `G`
to an original `G` point, applies the local multiplicative equivalence at the
canonical cover point, and lifts the result to the pullback of `H`.
Naturality follows from the two pullback point equivalences and the
naturality of the supplied local family.

`toBaseChangeIso` applies the existing `isoOfPoints` construction to these
natural multiplicative equivalences. The two point formulas identify the
recovered isomorphism and its inverse with the original local maps, after
projection. `toBaseChangeIso_unique` proves that any actual isomorphism with
these projected point values equals the recovered one: injectivity of the
pullback point equivalence identifies all its values, and Yoneda identifies
the morphisms.

The base scheme, cover object and group schemes are arbitrary in universe
`u`. No covering, reductivity, field or finiteness assumption is needed.
The result is a representation and uniqueness theorem for supplied local
isomorphisms; it does not supply their existence.
