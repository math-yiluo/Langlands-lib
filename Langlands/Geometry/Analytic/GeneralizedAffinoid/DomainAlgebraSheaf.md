# The stored algebra sheaf of all full affinoid domains

Author: Worker 36.

Fix a complete ultrametric normed field `K` and an actual presented affinoid
algebra `A` with arbitrary positive polyradius. `algebraSheaf` is a commutative
`K`-algebra sheaf on the independently constructed finite point-covering site of
all full represented domains over `A`. Its underlying presheaf is precisely
`algebraPresheaf`: the value at `U` is the original `U.algebra`, and every domain
arrow acts by its original stored bounded restriction. The displayed object,
map and whole-domain equations are definitional.

`algebraUnderlying_isSheaf` proves element descent on every covering sieve.
Choose a finite cover contained in the sieve. A compatible sieve family satisfies
the full represented-domain test equations for this cover. The finite algebra
gluing construction gives an element of the target's actual algebra. To check
its restriction at any other sieve arrow, pull back the finite cover's generated
sieve along that arrow and choose a finite cover contained in the pullback.
Each new arrow factors through an original component. Matching compatibility
and the already proved restrictions give equality after the new finite cover;
stored algebra separation gives equality on the entire new target. Uniqueness
follows from the original finite cover.

`algebraPresheaf_isSheaf` transports this result through the limit-preserving
forgetful functor from commutative `K`-algebras to types, using Mathlib's sheaf
criterion. Thus `algebraSheaf` uses a proved sheaf property and assumes no
descent result as an input.

This is an internal derivation from the existing stored presheaf, finite-domain
topology and finite stored-algebra gluing, with Mathlib's categorical sheaf
criterion. It invokes no additional original-source assertion or private peer
draft. It imposes no value-group, nontrivial valuation, reducedness, nonzero
algebra, or nonempty-spectrum or cover hypothesis. It concerns domains over one
fixed affinoid and does not construct a general analytic atlas or an etale or
equivariant site.
