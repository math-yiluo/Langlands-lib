# Integral representatives of rational action isomorphisms

This internal specialization of
`CategoryTheory.RationalizationEquivariantDenominators` uses actual abelian
schemes, their actual homomorphisms, and the existing rationalization of their
Hom groups. The base scheme and schemes retain their arbitrary displayed
universe.

`EquivariantRationalIsoIntegralData a a' e` is the generic exact equivariant
integral data specialized to integral ring actions on abelian schemes
`B` and `C` over the same scheme. It retains actual maps in both directions,
nonzero integer denominators, the prescribed rationalizations of those maps,
both exact inverse-multiple identities, and exact commutation with every
element of the integral ring in both directions.

`EquivariantRationalIsoIntegralData.baseChange` pulls supplied data back
along any actual scheme morphism. The existing
`RationalIsoIntegralData.baseChange` preserves its denominators,
rationalization identities, and exact inverse-multiple identities.
Applying the actual abelian-scheme pullback functor to each original
commutation equation proves exact equivariance for the pulled-back integral
actions. The four displayed projection lemmas record that the denominators
are unchanged and that the maps are the actual pulled-back maps.

For `O` a full integer lattice subalgebra of a rational algebra `A`,
and a finite integer basis `b` of `O`,
`integralActionRationalIsoData` takes an isomorphism between the rational
algebra actions obtained by extending two actual integral actions.
Its underlying rational isomorphism intertwines every element of `O`,
because the extension agrees there with the rationalized integral action.
The generic theorem therefore produces actual integral representatives
that intertwine every element of `O` exactly in both directions and retain
both exact inverse-multiple identities.

Base change transports supplied representative data. It makes no assertion
that independent choices made by `integralActionRationalIsoData` before and
after base change are equal. This construction assumes both integral
actions and their equivariant rational isomorphism as inputs. It does not
construct integral models for arbitrary rational actions or prove geometric
isogeny, polarization, adelic-level, or representability assertions.
