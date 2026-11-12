# Geometry of even paths and remaining-root orbit orderings

Provenance: internal. These interfaces package precisely the combinatorial data
needed to choose the even paths in the even-chain Galois-data construction.
They use the published `RootDatumPathWeights.IsPathComponent` predicate and
actual permutations of the simple-root support. They do not assert existence.

For a root datum `P` on an index type `I : Type u`, a simple-root base `b`, and
`J : Type u`, `EvenPathFamily b J` supplies a path of length `2 * half c` for
each `c : J`. Each path enumerates a type-A connected component, including
orthogonality to every simple root outside that component. Paths belonging to
different indices are disjoint. Positivity follows from `IsPathComponent.pos`.
No merged-root parametrization or reflection representative is part of this
structure.

`middleLeft` and `middleRight` are the vertices at positions `half c - 1` and
`half c`; `Rest` consists of the simple roots different from both vertices for
every selected path. `IsMiddleOut` reuses
`Langlands.GroupScheme.SplitPinning.middleDistance` from
[`EvenPathDistance`](EvenPathDistance.md), the same arithmetic definition used
by the even-chain product interface. Along each selected path, a remaining
vertex of strictly smaller distance must occur earlier. Equal distances
impose no order.

For a group homomorphism `ρ : Γ →* Equiv.Perm b.support`, a `CompatibleAction`
is an actual action on the path index type. It preserves path lengths, and for
each group element and path, it carries its ordered vertices either to the
ordered vertices of the image path or to their reversal. The Boolean choice is
inside each element/path pair; it is not required to be globally constant.

An `OrbitOrdering` gives an equivalence from a finite ordinal to `Rest`, proves
it is middle-out, and decomposes its enumeration as a list of orbit blocks. Each
block is invariant up to permutation after projection to the simple roots, all
of its members lie in one actual `ρ`-orbit, and any two distinct members are
orthogonal. The equivalence and flattening identity in particular exclude
repeated remaining roots and enumerate every remaining root. No commutation
between different blocks is asserted.

The lattice types and acting group can have universes different from that of
`I`; the path index type and remaining-root type use the universe of `I`.
Finiteness of `J`, compatibility of `ρ` with pairings, and existence of these
structures belong to the separate existence statement.
