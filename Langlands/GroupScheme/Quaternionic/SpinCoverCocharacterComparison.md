# Cocharacter comparison for the actual iterated split spin cover

This internal construction starts with a supplied spin cover, a supplied
orthogonal Morita comparison, a compatible field tower `K → F → L`, and an
actual torus map `i : T → G`. No splitting or maximality premise on `T` is
required.

`splitCoverTowerTorusMap` is the action of the iterated pullback of `T` in the
split orthogonal coordinates. It composes the iterated pullback of `i` with
the actual cover `splitCoverTower` and the identity-component inclusion.

`splitCoverTower_cocharacter` identifies the scalar extension to `L` of the
original cocharacter `nu → T → G → O(q)`, followed by the supplied Morita group
isomorphism, with the iterated scalar extension of `nu` followed by this torus
action. The implemented proof applies naturality of the actual
iterated-to-direct pullback comparison to `i ≫ pi`, and the canonical tower
formula for cocharacter-lattice base change. Both sides therefore refer to
the supplied maps, not to newly chosen representations.

The provenance is entirely internal: `SpinCoverScalarComparison` supplies the
actual cover and its factorization, and `Descent.cocharacterBaseChange_tower`
and `Descent.pullbackComparison_naturality` supply the two comparison identities.
No Morita existence, root normalization, eigenbasis or host vector-weight
statement is proved here. The fields, characteristic and universe remain
arbitrary.
