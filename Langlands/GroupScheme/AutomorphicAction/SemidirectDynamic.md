# Dynamic functors in the actual semidirect group scheme

Let `B : Scheme.{u}` be arbitrary, let `H` and `G` be group schemes over `B`,
let `a : AutomorphicAction H G`, and let `χ : (Gm B).toGrp ⟶ H` be any
cocharacter. The normal-factor inclusion into `a.semidirectProduct`
intertwines the restricted action `a.restrict χ` with ambient conjugation
through `χ ≫ a.semidirectInr`. All subgroup equalities below hold on every
test scheme over `B`.

Monomorphism of the inclusion identifies the fixed functor with the preimage
of the ambient dynamic centralizer. When `H.X.hom` is separated, the inclusion
is closed, and equivariant lifting of affine-line orbit extensions identifies
the parabolic and identity-limit functors with the preimages of the ambient
parabolic and unipotent functors. These arguments use the published
`Dynamic.ActionFunctoriality` interface and the action/conjugation comparison.

If `H.X` is a commutative group object, the semidirect projection is invariant
under this ambient conjugation action. If `H.X.hom` is also separated, its
value at a point with identity limit must be the identity: uniqueness of
extensions into the separated target gives the invariant-morphism result
from `Dynamic.ActionUniqueness`. Thus the whole ambient unipotent functor
lies in the range of the normal-factor inclusion. Combining that containment
with the preimage equality shows that the image of the original identity-limit
functor is exactly the ambient unipotent functor.

Under these commutativity and separation assumptions, suppose an actual
homomorphism `j : U ⟶ a.semidirectProduct` represents the ambient unipotent
functor. The construction `semidirectUnipotentLift` factors `j` through the
normal factor. It applies the represented-subgroup Yoneda lifting construction
to the inclusion of the ambient unipotent functor into the range of
`a.semidirectInl`. The theorem `semidirectUnipotentLift_comp` identifies the
composite with `j`. Cancellation by the monomorphic normal-factor inclusion
then proves that this lifted homomorphism represents `(a.restrict χ).unipotent`.
If `j` is a closed subgroup inclusion, its lift is closed by cancellation of a
separated postcomposition. The representative is the same group scheme `U`,
so any properties of its scheme, such as smoothness and connectedness, are
retained without any isomorphism choices.

This is internal derived content from the actual semidirect construction,
equivariant orbit-extension transfer, invariant-map uniqueness, and represented
subgroup lifting. It asserts no external source theorem. Existence of an ambient
representative, its smoothness or connectedness, and Lie-weight comparisons
remain separate inputs; this module does not prove the cyclic-tail comparison.
