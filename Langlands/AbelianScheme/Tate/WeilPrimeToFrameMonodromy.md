# Geometric monodromy on prime-to-modulus Weil-compatible frames

This module constructs the geometric action and fixed right orbits for the
actual prime-to-modulus Weil-compatible frame space. Its explicit theorem
dependency is `RationalWeilGeometricTransportStatement`. It does not prove
that proposition. The motivating sources are Harris–Taylor, *The Geometry
and Cohomology of Some Simple Shimura Varieties* (2001), III.1, pp.91–92,
and Kottwitz, *Points on some Shimura varieties over finite fields* (1992),
Section 5, pp.390–391.

Let `m` be an arbitrary modulus. The constructions use the existing ring
`PrimeToFiniteAdeles m`, the actual rational Tate module and root twist
with orders coprime to `m`, and the actual pairing
`awayAdelicWeilAlongHomBilinearMap`. The same coupled scalar comparison
`hAway` is used on the inputs and the twist. Invertibility on the base and
root finite étaleness are required only at the retained orders.

`weilPrimeToFiniteAdeleTwistedMonodromyRepresentation` pairs the actual
tensor-algebra-linear Tate monodromy with the actual section-ring root
monodromy. Its values preserve the pairing into the twist jointly.
The preservation proof applies the displayed geometric compatibility
proposition to a loop and the coprime-order predicate. The representation
laws follow from the two constructed representations.

`weilPrimeToAdelicFrameMonodromyAction` uses this representation to
postcompose the actual `WeilPrimeToAdelicFrame`. It also postcomposes the
existential trivialization in the form-compatibility proof with the
actual twist monodromy. The root action is retained and no roots or twist
basis are chosen. `weilPrimeToAdelicFrameActionsComm` verifies that target
postcomposition commutes with right source-similitude precomposition by
checking the underlying maps.

`WeilPrimeToAdelicLevel U` is the subset of right `U`-orbit classes fixed
by the actual geometric fundamental group, using `PEL.InvariantOrbit`.
The definition does not require a representative fixed by that group.
It is available for any source-similitude subgroup `U`; compact open
subgroups are special cases when their topology and compact openness
are supplied by a PEL specialization. When `m` is prime this is the
prime-to-that-prime construction.

The dual/Poincaré data, rational source form and actual dual-valued
homomorphism retain the generality of `WeilPrimeToAdelicFrame`. The
polarization predicate and finite-dimensional, faithful, involution,
alternation and nondegeneracy conditions belong to the intended PEL
application. This unit does not prove nonemptiness, compact openness,
existence of paths, canonical change of base point or construction of
an unpointed moduli functor. It is a derived actual-geometric
construction conditional on a named compatibility proposition, with
no arbitrary pairing or replacement monodromy.
