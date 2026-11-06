# An open self-centralizing split-torus locus in actual fibres

Let `R` be any commutative ring, let `G` be a smooth affine group
scheme over `Spec R`, and let `i : Gm^I → G` be an actual
closed group-scheme immersion, for a finite index type `I`.
The fibres of `G` need not be connected.

For a point `s`, `geometricIdentityComponentHom` is an actual
homomorphism from the standard split torus over the chosen
algebraic closure of the actual residue field into
`identityComponent (geometricFiber G s)`. First pull back the
specified `i` using the existing pullback functor and its
split-torus comparison. Then factor that map canonically
through the existing identity component. Its composite with
the actual identity-component inclusion recovers exactly the
specified geometric-fibre torus map. The resulting map is
a closed immersion.

`geometricSelfCentralizingTorusLocus` consists of those `s`
where the existing all-test centralizer of this map, computed
in the actual geometric identity component, equals its
existing all-test range. The file proves this locus is open
over arbitrary rings, including nonnoetherian and nonreduced
rings. Every torus at a point of this locus is maximal
in that geometric identity component.

The proof gives an exact membership criterion. By the actual
identity-component weight comparison and the actual geometric
weight-rank comparison, the zero-weight dimension in the
identity component equals the relative exponent-weight rank
at exponent zero. The Lie dimension of the standard split
torus is `Nat.card I`. If the torus is self-centralizing,
the existing zero-weight differential is a linear equivalence,
so those dimensions agree. Conversely, equality of dimensions
implies self-centralizing equality by `SelfCentralizingFromLie`,
applied to the smooth connected actual identity component.
Thus the locus is exactly the fibre where the relative
zero-weight rank equals `Nat.card I`. That relative rank
is locally constant, so this fibre is open.

The provenance is internal: the construction and proof combine
the existing actual pullback, torus and identity-component
maps with the previously constructed actual relative weight
ranks, their geometric-fibre comparison, the actual
identity-component weight equivalence and the zero-weight
self-centralizer criterion. It implements the local
maximality control needed after a fibre torus has been lifted.
The torus `i` is an explicit input to this intermediate
result. Its construction from reductivity at one fibre,
the rank-one reduction and openness of the reductivity
locus remain separate obligations of the unchanged main task.
