# Free vector groups as finite free additive bundles

Author: Worker 590, in collaboration with Worker 204 on Task 7200.

## Construction and scope

This internal derived construction compares the polynomial vector group over
an arbitrary commutative ring with the additive sections of one actual finite
free structure-module sheaf. All declarations are universe-polymorphic at
`u`. The ring may be the zero ring, the base may be empty, and the rank `n`
may be zero.

For any scheme `S`, `freeBundle S n` is the actual sheaf
`SheafOfModules.free` on the finite index type `ULift (Fin n)`.
`isFiniteLocallyFree_freeBundle` uses its generating sections and their
restriction to each open to supply the existing `IsFiniteLocallyFree`
predicate, including finite local generator data and local bases.

For every test scheme `T` over `S`, `freeBundleBasis n T` is the
`Fin n`-indexed basis of global sections of the actual pullback of
`freeBundle S n`. It comes from the canonical `freePullbackIso` and
`globalSectionBasis`, with the lifted indices removed. The basis-application
lemma identifies each vector with the pullback of the original free
generator. The basis-naturality lemma then applies the published
`AffineSectionCoordinates.sectionPullback_pullbackSection` comparison.
Despite that namespace's name, this comparison and the present construction
apply to all test schemes.

`freeBundleSectionEquiv` is the resulting additive equivalence from
`Fin n → Γ(T.left, ⊤)` to these global sections. Its finite-sum formula,
the basis-naturality lemma, and semilinearity of the exact
`RelativeUnipotent.sectionPullback` prove its naturality for every
morphism of tests.

## Point equivalences and the vector-bundle predicate

The selected data definition `freeVectorBundlePoints R n T` composes
`VectorGroup.coordinates` with the multiplicative form of
`freeBundleSectionEquiv`. Its source is the group of all `T`-points of the
polynomial vector group over `Spec R`; its target is the multiplicative
type tag of the additive global sections of the pullback of the same free
sheaf. `freeVectorBundlePoints_natural` combines coordinate naturality
with the preceding finite-sum argument.

`isVectorBundleAdditive_vectorGroup R n` verifies the unchanged
`IsVectorBundleAdditive (VectorGroup.groupScheme R n)`. Affineness
comes from the spectrum map; smoothness comes from the published
corepresented polynomial group and its smoothness criterion. The remaining
conjuncts use the actual free sheaf, its finite local bases, and the all-test
natural point equivalences above. No field, noetherian, or nonempty-base
hypothesis is added.

## Isomorphism transport

`vectorBundlePointsOfIso e M c` transports supplied point equivalences
through a group-scheme isomorphism `e : V ≅ W`, by composing a point of
`W` with `e.inv`. The module sheaf `M` and its section pullbacks are
unchanged. The application lemma gives this formula directly.

`IsVectorBundleAdditive.of_iso` transports the full predicate from `V`
to `W`. The underlying scheme isomorphism preserves affineness and
smoothness. Associativity of composition transports the all-test
naturality equation, using exactly the same finite locally free sheaf.

## Provenance and retained obligations

This unit is derived from the Library's actual free module-sheaf pullback
and basis APIs, the exact relative-section comparison, and the polynomial
vector group's all-test coordinates. It formalizes the direct
finite-free construction rather than an additional claim from an external
source. It supplies a building block for Task 7200; constructing and
descending the radical filtration and proving its termination remain
separate obligations.
