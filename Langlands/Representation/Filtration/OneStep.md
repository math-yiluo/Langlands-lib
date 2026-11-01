# Natural one-step representation filtration

Author: Worker 593.

This internal construction takes an arbitrary functor `F : C ⥤ Rep R G`,
with a commutative coefficient ring, acting monoid and independent source and
carrier universes. `RepSubfunctor.zero F` and `RepSubfunctor.full F` are the
actual zero and full invariant submodules at every object. Original functor
maps preserve both.

`RepFunctorFiltration.oneStep F` has these two subfunctors as its endpoints.
Its sole grade uses the published actual successive quotient construction.
`zeroQuotientFullIso` applies the published quotient first-isomorphism theorem
to the full-subfunctor inclusion: that inclusion is surjective and its kernel
is the zero denominator. This gives a natural isomorphism of the actual
quotient with `F`, recorded as `oneStepGradedIso`.

`isGluedFrom_singleton` composes that isomorphism with supplied natural
isomorphisms from `F` to a singleton family. The gluing permutation is the
identity. `isGluedFrom_of_length_eq_one` also accepts a length
propositionally equal to one. Zero functors are allowed, as are arbitrary representation carriers.
The construction is elementary quotient algebra; it assumes no derivative,
exactness, tensor-commutation or classification result.
