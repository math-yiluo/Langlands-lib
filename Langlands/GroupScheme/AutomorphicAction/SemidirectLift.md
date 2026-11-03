# Lifting a commuting action to a semidirect product

This internal construction is over an arbitrary base scheme and universe.
The group schemes `K` and `L` act on `G` through actual actions `a` and `b`.
The explicit commuting hypothesis says, on every test scheme and for every
acting and normal point, that applying `b` after `a` equals applying `a`
after `b`.

`semidirectLiftHom` is the actual scheme morphism which applies `b` to the
normal coordinate of `a.semidirectProduct` and retains its acting coordinate.
The coordinate evaluation formula follows from precomposition naturality and
the product projections. Under the commuting hypothesis, `semidirectLift`
packages this morphism as an automorphic action of `L`. The unit and action
composition laws follow from those of `b`. Preservation of the semidirect
group law uses preservation of normal multiplication by `b` and commutation
with `a`.

The canonical normal inclusion intertwines `b` and this lifted action.
Every point of the acting-factor inclusion is fixed, and the canonical
projection to the acting factor is invariant. For a second normal group with
two commuting actions, an actual homomorphism equivariant for both actions
induces a semidirect map equivariant for the lifted actions. These assertions
are proved by applying the multiplicative semidirect coordinate equivalence
on an arbitrary test scheme and comparing its two coordinates.

The provenance is internal, from the existing actual semidirect product,
its canonical maps and its equivariant map construction. No field, affine,
smoothness or connectedness assumption is imposed. In particular this unit
does not prove existence of a solvable decomposition, stability or realization
of semigroup factors, scalar descent, or the host ordered-product proposition.
