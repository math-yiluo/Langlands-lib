# Actual relative roots through the full-kernel identity component

This internal construction works over an arbitrary field `k : Type u` and
arbitrary universe `u`. It uses an actual split torus `T`, a character `a`,
and a homomorphism `j : C → G` representing the full scheme-theoretic
character-kernel centralizer. The group `C` is smooth and affine. Where
root-functor comparison is asserted, `j` is also a closed subgroup inclusion.
The character morphism is quasi-compact, flat and surjective. These three
properties are supplied by the published `RelativeRoot.characterFpqc` for
every nonzero character of the split torus, including divisible characters.

`SubgroupFunctor.map_comp` identifies successive all-test images with the
image under the composite group homomorphism. Its proof composes and
reassociates the actual witnesses of subgroup membership.

`AutomorphicAction.IsEquivariant.unipotent_map_identityComponent` applies
to any pair of actual multiplicative-group actions on a smooth affine group
and its actual identity component, provided their inclusion is equivariant.
The published closed-subgroup transfer theorem identifies the image of the
component's identity-limit functor with the intersection of the ambient
identity-limit functor and the component range. The identity-zero affine-line
lifting theorem puts every ambient identity-limit point in that range.
Thus this image is the entire ambient identity-limit functor. This uses no
connectedness or representability assumption on the identity-limit functor.

`kernelCentralizerIdentityQuotientAction_isEquivariant` bundles the previously
proved inclusion-equivariance equation for the actual descended actions.
`kernelCentralizerIdentityQuotientAction_unipotent_map` specializes the general
identity-component comparison to those actions. Combining it with the published
`RelativeRoot.quotientActionComparison` and the image-composition law proves
`kernelCentralizerIdentityQuotientAction_comparison`: the original actual root
subgroup is exactly the image of the identity-limit functor of the descended
action on `C⁰`, under the actual composite `C⁰ → C → G`.

`kernelCentralizerIdentityRootPointsMap` is that inclusion on groups of points.
`kernelCentralizerIdentityRootPointsEquiv` makes it a multiplicative equivalence
on every test scheme. The composite inclusion is monomorphic, giving
injectivity; the all-test root-functor comparison gives surjectivity. Its
application formula is exactly postcomposition with the two actual inclusions.
Tests may be disconnected and nonreduced.

The provenance is internal composition of the published actual action,
equivariant closed-subgroup transfer, root-functor comparison and identity
component constructions, together with the affine-line identity-limit lift.
The full character kernel is retained throughout. This module asserts no
intrinsic centralizer reductivity, root movement, parabolic minimality or
normalizing representative existence.
