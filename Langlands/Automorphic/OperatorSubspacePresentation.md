# Actual presentations for invariant subspaces of operator quotients

This internal derived construction begins with an actual automorphic operator
quotient `Q` and an invariant subspace `P` of its whole-operator representation.
It constructs a new actual automorphic numerator/denominator presentation whose
whole-operator representation is genuinely equivalent to `P.toRepresentation`.
The field has arbitrary universe, the rank is any natural number, and the
coefficients are complex.

`subspaceUpper` pulls `P` back through `Q.projection` and maps that preimage
through the faithful inclusion of the original numerator into stable
automorphic forms. Thus its vectors are actual stable forms, and its defining
condition on a vector from the original numerator is exactly that its quotient
class belongs to `P`. Projection covariance and the original inclusion's
covariance prove invariance under the entire concrete operator algebra.
`subspaceUpper_le_upper` proves containment in the original actual numerator.
The resulting numerator inclusion is injective and equivariant.

`subspaceNumeratorMap` restricts the original quotient projection to this new
numerator and restricts its target to `P`. The exact defining membership
condition makes this target restriction legitimate. Every vector of `P` has
a representative in the old numerator, and that representative belongs to
the new numerator, so the restricted projection is surjective.

`subspacePresentation` uses this actual numerator and the genuine invariant
kernel of its restricted projection. The proved denominator membership
criterion identifies it exactly with the restriction of `Q.lower` along the
new numerator inclusion. The published equivariant quotient lift defines
`subspaceMap` into `P.toRepresentation`. Mathlib's exact kernel theorem for
`Submodule.liftQ` proves injectivity; surjectivity follows from that of the
restricted numerator projection. The genuine intertwiner `ofBijective`
construction then gives `subspaceEquiv`, with an exact formula on numerator
representatives.

`subspaceInclusion` composes this descended map with the actual inclusion of
`P` into `Q.Space`. It is injective, has invariant range exactly `P`, and
sends the new class of a numerator vector to its original quotient class.
Thus this unit constructs a presentation of every supplied invariant subspace,
not merely a relation asserting that such a presentation exists.

Provenance is internal: this is the subspace form of the module quotient
correspondence applied to the published actual automorphic quotient and its
faithful numerator inclusion. The construction directly reuses Mathlib
submodule preimage, image, inclusion and kernel, the published equivariant
quotient lift, and genuine representation equivalences. It imports only
`Langlands.Automorphic.OperatorSubquotient`; no pending image, compatible-map
or lattice-correspondence candidate is required.

No nonzero subspace, irreducibility, cuspidal or spectral existence is assumed
or constructed here. The quotient is not embedded into the function space,
and no evaluation or topology on quotient vectors is supplied. Its numerator
is an actual subspace of the original forms, while the proved quotient
embedding has target the original quotient.
