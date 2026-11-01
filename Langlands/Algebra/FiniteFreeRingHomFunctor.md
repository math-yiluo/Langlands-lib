# Natural finite equations in a ring-valued functor

This internal construction promotes the proved equivalence in
`Langlands.Algebra.FiniteFreeRingHom` to a natural isomorphism.
Let `b : Basis I ℤ O` be a finite integer basis of a possibly
noncommutative unital ring `O`, and let `R : C → RingCat` be any
ring-valued functor on any category `C`.

`actionFunctor b R` assigns the universe lift of the set of actual unital
ring homomorphisms `O →+* R(X)` to `X`. A morphism `f : X → Y` acts by
unwrapping, postcomposition with the ring homomorphism `R(f)`, and
rewrapping. `solutionsFunctor b R` assigns the universe lift of the
existing subtype of tuples `(r_i)` satisfying

`∑ i, b.repr(1)_i • r_i = 1`

and, for every ordered pair `i,j`,

`∑ k, b.repr(b_i*b_j)_k • r_k = r_i*r_j`.

Its morphism map unwraps the tuple, applies `R(f)` to every entry,
and rewraps it. The existing
`FiniteFreeRingHom.map` proves that all relations remain satisfied.
Both functors use `ULift.{max uI uO uR}` to place their values in the
common universe `max uI uO uR`. This is a size adapter with the canonical
unwrap/rewrap equivalences; it does not identify the independent
universes of the basis index, the order and the target rings.

`actionSolutionsIso b R` conjugates the existing basis-value equivalence
by these canonical size equivalences at every component.
After unwrapping, its forward map evaluates an action at each `b_i`;
its inverse evaluates at `x` by the finite integer-linear sum
`∑ i, b.repr(x)_i • r_i`. Naturality is precisely the proved
`equiv_natural`: postcomposition of an actual action has the same
basis values as applying the target ring map to its tuple.
The functor laws follow from the identity and composition laws of `R`.

The provenance is internal categorical packaging of the published
finite-equation construction. No representability, geometry, freeness
of a new ring, or existence of a ring action is asserted.
