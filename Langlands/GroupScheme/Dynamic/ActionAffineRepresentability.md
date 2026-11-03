# Closed affine representatives for Gm-action identity-limit functors

This internal construction applies to an arbitrary automorphic action `a` of the actual multiplicative group on an affine group scheme `G` over `Spec R`, where `R` is any commutative ring in universe `u`. It constructs a closed affine group scheme representing `a.unipotent` on every scheme over the base. No smoothness, connectedness, or representability of `a.unipotent` is assumed for this construction.

`AutomorphicAction.restrict_id` first identifies restriction along the identity group homomorphism with the original action. Its proof simplifies the identity whiskering in the action morphism; the remaining structure fields are propositions.

In `AutomorphicAction.Affine`, the scheme `unipotentScheme a` is the existing `Dynamic.Affine.unipotentScheme` for the cocharacter given by the acting-factor inclusion into the actual semidirect product `G ⋊ Gm`. The multiplicative group is affine and separated, so the semidirect product is affine and its ambient dynamic unipotent scheme is available. The commutativity and separation hypotheses needed for the semidirect transport lemmas hold for `Gm`.

`unipotentHom a` factors the ambient unipotent inclusion through the normal-factor inclusion into the semidirect product, using `semidirectUnipotentLift` and the ambient representative theorem. `unipotentHom_comp_semidirectInl` states the resulting exact factorization. The same representing scheme is used throughout.

`isRepresentedBy_unipotentHom` applies the semidirect representative-transfer theorem with the identity cocharacter of `Gm`, then simplifies `restrict_id`. Thus the factored homomorphism represents the original action's identity-limit subgroup functor on all tests. `isClosedSubgroup_unipotentHom` transfers the closedness of the ambient dynamic inclusion through the separated normal-factor inclusion. Its composite with the affine structure morphism of `G` is affine, giving the instance `unipotentScheme_isAffineHom`. The theorem `unipotent_isClosedRepresentable` packages the constructed representative and its closedness.

Over any field, when `G` is smooth, `smooth_unipotentScheme` applies the published `dynamicSmooth` theorem to the semidirect product, whose underlying scheme is the product of the smooth schemes `G` and `Gm`. This proves smoothness of the same constructed representative. `smooth_of_isRepresentedBy_unipotent` transfers it to every other representative via the canonical represented-subgroup isomorphism and smoothness under an isomorphism over the base.

`connected_unipotentScheme` is explicitly conditional on `DynamicConnectedStatement.{u}`. It applies that statement's unipotent clause to the semidirect product; connectedness of `G` is not required. `connected_of_isRepresentedBy_unipotent` transfers this conditional connectedness to any representative using the underlying homeomorphism of its represented-subgroup isomorphism.

The proofs are derived from the existing actual semidirect group scheme, all-test orbit-extension and represented-subgroup constructions, affine dynamic representability, and published dynamic smoothness. They assert no additional literature theorem. In particular, this module does not prove `DynamicConnectedStatement`, a Lie-weight comparison, or the host `CyclicRootFunctorComparisonStatement`; those remain separate obligations.
