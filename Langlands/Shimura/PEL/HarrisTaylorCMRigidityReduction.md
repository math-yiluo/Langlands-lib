# A conditional reduction of exact CM small-level rigidity

This internal unit isolates the remaining finite-order obligation on the actual
objects and proves a conditional reduction to the unchanged published rigidity
target. It retains the target's universes and all named geometric prerequisites.

`CMCoarseLevelFiniteOrder` uses the same positive polarized action objects,
positive-object and numerical tests, original Harris level orbits, rational
self-isogenies and polarization-multiple equations as
`CoarseLevelHasNoAutomorphisms`. Its conclusion is finite order of the actual
rational endomorphism underlying the self-isogeny. It is a proposition target,
not a proof of finite order. `CMGeometricCoarseFiniteOrder` tests it at every
admitted algebraically closed field spectrum, with the identity geometric point
and the same admissibility instances. `CMSmallLevelFiniteOrderStatement`
restricts this assertion to every original sufficiently small level.

`cmSmallLevelRigidity_of_finiteOrder_and_primeFaithfulness` assumes that
finite-order target and injectivity of the actual rational prime Tate action on
rational endomorphisms over every algebraically closed characteristic-zero
field and every prime. The latter is an explicit premise; this unit does not
supply a new faithfulness target or prove that geometric theorem.

The implemented proof unfolds the exact published rigidity target and fixes
one of its tested objects. The structural morphism from the CM field induces
an injective field map, which gives characteristic zero of the test field.
The finite-order premise supplies actual finite order for this fixed orbit.
Sufficient smallness selects a finite place. The proved Harris prime-operator
identity then makes the actual prime Tate map of the self-isogeny equal to the
identity map. The assumed injectivity gives identity of the underlying
rational homomorphism. The existing action-object homomorphism extensionality
and isomorphism extensionality give the required identity self-isogeny.

This is an internal logical reduction through the imported actual
constructions. It does not prove finite order, Rosati positivity, multiplier
positivity, a lattice realization, polarized automorphism finiteness, or
one-prime faithfulness. The original `CMSmallLevelRigidityStatement` and its
imports remain unchanged. The conditional theorem alone does not discharge
the main rigidity task.
