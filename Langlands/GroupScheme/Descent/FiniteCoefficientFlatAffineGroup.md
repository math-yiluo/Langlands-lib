# Finite coefficient models of affine flat finitely presented groups

This is an internal construction from the published finite
coefficient descent theorems for affine schemes, group laws and flatness.

For commutative rings `R` and `A` in the same arbitrary universe, with an
`R`-algebra structure on `A`, `FlatAffineGroupModel R A G` records a finitely
generated coefficient subalgebra of `A`, an affine flat finitely presented
group over it, and an actual group-scheme isomorphism recovering `G` after
base change to `A`. If `G` is commutative, the model is commutative.

`exists_flatAffineGroupModel` also ensures that the coefficient subalgebra
contains any prescribed finite subset of `A`. It first descends the underlying
affine finitely presented scheme, then its full group law. The published
flatness descent theorem permits a further finite coefficient enlargement.
Base change preserves the affine and finite-presentation properties.
Transitivity of finite type combines the nested coefficient subalgebras.
The direct-versus-iterated pullback comparison gives the final recovery
isomorphism.

`flatAffineGroupModel` chooses a model. `FlatAffineGroupModel.noetherian`
proves that its coefficient ring is noetherian whenever `R` is noetherian.
Taking `R` to be a copy of the integers in the chosen universe therefore
provides noetherian models for the groups used in the relative
multiplicative-type extension argument.

This construction does not descend a supplied diagram of homomorphisms or
its exactness, and does not assert that a model of a multiplicative-type
group is already of multiplicative type.
