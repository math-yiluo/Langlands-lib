# Commutator maps on actual relative root groups

This internal construction defines `AutomorphicAction.commutatorMap` for any
automorphic action `a` of a group scheme `H` on a group scheme `V` over an
arbitrary scheme in universe `u`, and a section `t` of `H`. On every scheme
test it sends `x` to `a.act(t,x) * x⁻¹`. Pullback along any base morphism
preserves this scheme map, with the section transported by
`baseChangeBasePoint`.

If homomorphisms `H → G` and `V → G` identify the action with conjugation,
the image of this map in `G` is the ordinary commutator `[t,x]`. The module
proves this formula both over the original base and after arbitrary base change.
These proofs use the multiplicative pullback point equivalence, naturality of
the action and constant points, and preservation of group operations by the
inclusion homomorphisms.

`LocalRootGroup.rootCommutatorMap` specializes this construction to the actual
dynamic group `Uc i mu nu` over an arbitrary commutative ring `R`. Here `I` is
a finite coordinate type, `G` is an affine group scheme over `Spec R`, and `i`
is a homomorphism from the coordinate split torus to `G`. Its ambient formula
uses the published full-torus action on the dynamic group and its inclusion in
`G`. No reductivity, local-ring, reducedness, characteristic or weight hypothesis
is required for this construction or formula.

The auxiliary theorem `isIso_of_scalar_points` assumes an actual group-scheme
isomorphism `Ga R ≅ V` and that, on every scheme test, an endomorphism `f` acts
in these coordinates by multiplication by a unit in global functions. It proves
`f` is an isomorphism by Yoneda: the additive coordinate equivalence transfers
the bijectivity of multiplication by a unit to postcomposition with `f`.

The provenance is internal: these are formal consequences of the published
automorphic action, point functor, pullback equivalence and dynamic torus
action. This module does not assert that a particular root commutator map is
invertible, or prove relative semisimple fppf-perfectness.
