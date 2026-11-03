# Intrinsic root functors in the full-kernel identity component

This internal comparison identifies the root functor defined by the actual
lifted torus inside the actual identity component with the original root
functor in the ambient group. It works over an arbitrary field in arbitrary
universe `u`. The represented full character-kernel centralizer `C` is smooth
and affine. Its inclusion `j : C → G` is closed where the ambient comparison
is asserted. The character morphism is quasi-compact, flat and surjective;
the published `RelativeRoot.characterFpqc` supplies these properties for every
nonzero character of the split torus. No primitivity hypothesis is used.

The first three lemmas work over any base scheme. Suppose an actual action `b`
of the multiplicative group on `H` restricts through the actual character `a`
to conjugation by `i : S → H`. Then `whiskerLeft_descendedAction_orbit`
identifies the pulled-back action orbit with the torus-conjugation orbit.
`isOrbitExtension_iff_descendedAction` proves that the same affine-line family
extends either orbit. The forward implication checks equality after locally
lifting the acting point through the fpqc character; it does not require a
lift on the original test scheme. The reverse implication composes with the
character. The zero value of the family is unchanged. Thus
`subgroup_eq_unipotent_of_restrict` identifies the intrinsic root subgroup
functor and the action's identity-limit subgroup functor on all test schemes.

`kernelCentralizerIdentity_subgroup_eq_unipotent` applies this to the actual
descended action on `C⁰` and its proved restriction equation.
`kernelCentralizerIdentity_subgroup_map` then uses the established component
image comparison: the root subgroup computed using the lifted torus in `C⁰`,
and included by `C⁰ → C → G`, is the original root subgroup.
`kernelCentralizerIdentityIntrinsicRootPointsEquiv` is the resulting
multiplicative equivalence on points of every test scheme. Its application
formula is exactly postcomposition with the actual inclusions. Tests may be
disconnected or nonreduced.

The provenance is internal composition of actual orbit definitions, fpqc
local-lift equality, the constructed descended action and the component image
comparison. The full scheme-theoretic character kernel and the original
character lattice remain unchanged. No centralizer reductivity, relative-root
Lie comparison, root movement or opposing-parabolic existence is asserted.
