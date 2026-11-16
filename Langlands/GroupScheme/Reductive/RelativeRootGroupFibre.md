# Field fibres of actual relative dynamic root groups

This internal comparison concerns the published actual dynamic group
`Uc i mu nu`, formed inside the dynamic centralizer of `mu`. Its context is an
arbitrary commutative ring `R` in universe `u`, a group scheme `G` over `Spec R`
with affine structure morphism, a finite coordinate type `I`, a homomorphism
`i` from the coordinate split torus to `G`, and integer exponent vectors `mu`
and `nu`. It imposes no locality or reducedness condition on `R`.

`fibreRootMap` composes an additive-group isomorphism of its base change to a
given field `K` in universe `u` with its supplied `R`-algebra structure, with the
actual base-changed subgroup inclusion. The equality
`fibreRootMap_eq` identifies that composite with the base change of `incl`.
Given the field-fibre equivariance supplied by `LocalRootGroup.exists_fibreIso`,
the resulting map is a closed root parametrization on every scheme test,
provided the root vanishes on `mu` and has positive pairing with `nu`.

To prove equality with the actual root subgroup, equivariance first places the
image in the root subgroup. In the other direction, a root-subgroup point
centralizes `mu` and contracts under `nu`. The actual representatives of the
centralizer and its dynamic unipotent group therefore lift it, and the inverse
additive-group isomorphism supplies its root coordinate. Closed immersion is
preserved under the subgroup compositions and the isomorphism.

`exists_rootFibreParametrization` additionally assumes `IsReductive G`, that `i`
is a fibrewise maximal torus, a fibrewise full coordinate root datum `P`, and a
root `α` of `P`. The supplied vector `mu` must annihilate `P.root α`, and every
root it annihilates must equal that root or its negative. With `nu` equal to
`P.coroot α`, the theorem uses the published rank-one field-fibre theorem and
the root-coroot pairing two. Reductivity supplies the smoothness needed by that
field-fibre theorem. Its output is both an actual additive-group
isomorphism of the base-changed `Uc` and an exact root parametrization of its
composite inclusion in the base-changed ambient group. This module constructs
field-fibre parametrizations; it does not claim a global additive coordinate.
