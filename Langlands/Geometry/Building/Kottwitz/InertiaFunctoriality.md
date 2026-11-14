# Functoriality of inertia coinvariants

This internal construction supplies the quotient argument for the torus inertia
comparison in `FundamentalGroupStatement`. It derives its results from the
published definitions in `InertiaCoinvariants` and Mathlib's actual
representation coinvariants; no additional geometric or source assertion is
introduced.

Let `k → K → E` be a compatible tower of fields with `K/k` normal, and let
`ρ`, `τ` be integral representations of `Aut_k(E)`, with arbitrary carrier
universes. `inertiaMap` restricts an actual intertwiner to the kernel of
restriction to `K`, then applies `Representation.Coinvariants.map`. Its
`inertiaMap_projection` formula sends the class of `x` to the class of `f x`.
`inertiaMap_unique` and `inertiaMap_existsUnique` establish that this formula
determines the map uniquely, using the quotient's linear-map extensionality.
The identity and composition laws are checked on original representatives.

`inertiaEquiv` applies this construction to a representation equivalence and
its inverse. Both inverse identities reduce on representatives to the
original equivalence identities. Its representative formula is recorded by
`inertiaEquiv_projection`.

When `E/k` is also normal, `inertiaMap_equivariant` proves equivariance for the
actual residual group `Aut_k(K)`. Restriction surjectivity lifts a residual
automorphism to `Aut_k(E)`, quotient projection surjectivity supplies a vector
representative, and `inertiaGammaRepresentation_restrict` reduces the desired
identity to the original intertwining law. `inertiaRepresentationEquiv`
packages the resulting equivalence of residual representations.

No separable-closure, torus or local-field hypothesis is needed for this
quotient construction. Its role in the task is to descend the separately
proved canonical torus fundamental-group comparison and its inverse.
