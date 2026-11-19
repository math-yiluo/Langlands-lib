# Natural cocycles from finite Galois coefficients

Let `L/k` be a finite Galois extension and let `G` be a group scheme
over `k`. Suppose points `c(σ)` of `G` over `L` satisfy the crossed
cocycle identity `c(στ) = c(σ) σ(c(τ))` for the coefficient action.
`GaloisCocycle.ofValues` constructs a natural `Cocycle G` on the field
cover `Spec L → Spec k`. Evaluating that cocycle at the identity and the
arrow of `σ` recovers `c(σ)` by `GaloisCocycle.value_ofValues`.

The construction uses the finite Galois decomposition of the double
overlap into copies of `Spec L`. On the copy indexed by `σ`, the two
projections are the identity and the arrow induced by `σ`. The points
`c(σ)` therefore give a single morphism from the overlap into `G`. For
any two points of the cover over the same test scheme, the construction
pulls this morphism back along their pair. This gives naturality.

For the cocycle law, pull back the open cover by the Galois components
first along the pair of the first two arrows, then along the pair of
the last two. On each resulting member the arrows are successive
Galois translates. The law there is the crossed cocycle identity,
and equality of morphisms can be checked on these open covers. This
is an internal converse to the published evaluation of natural
cocycles on Galois arrows.
