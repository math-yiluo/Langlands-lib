# Local trivialization of the actual associated etale coefficient sheaf

Author: Worker 149.

`Langlands.Shimura.Coefficients.etaleAssociatedTrivialization` proves exactly
`Langlands.Shimura.Coefficients.EtaleAssociatedTrivializationStatement.{u}`.
It retains every quantifier of the published target: a scheme `X`, a group
`G`, an action `Y` on `X.Etale` satisfying `IsFiniteGeometricTorsor X Y`,
and a commutative coefficient ring `R`, all at the target's arbitrary
universe `u`.

The conclusion is existence of a natural isomorphism from
`etaleAssociatedFunctor X Y` followed by restriction to the localized
small etale site over `Y.V`, to the functor that forgets the coefficient
representation's action, forms its constant sheaf on `X`, and restricts
that sheaf to the same localized site. The restriction functor is
`(Scheme.smallEtaleTopology X).overPullback (ModuleCat R) Y.V`.
The isomorphism is natural in every equivariant coefficient map.

The implemented proof composes two existing Library results.

1. `etaleTorsorSectionSplitting X G Y hY R` proves the graph restriction
   bijection for every `R`-module sheaf and every `U : Over Y.V`, using
   only the given geometric torsor hypothesis. The graph indexed by `g`
   is `prod.lift (U.hom ≫ Y.ρ g) (𝟙 U.left)`. Its proof derives a
   covering by these graphs and empty overlaps for distinct indices,
   then applies sheaf gluing.
2. `constantAssociatedTrivializationOfSplitting` takes exactly that
   splitting property and constructs the required natural isomorphism.
   Its underlying map restricts an invariant section to the identity
   graph. Graph splitting reconstructs the invariant section from its
   value there; this construction is natural in coefficient maps.
   Applying it to `Scheme.smallEtaleTopology X` and `Y` therefore gives
   a witness for the target's `Nonempty` conclusion.

No graph decomposition, section-splitting witness, action-map
isomorphism, or trivialization is an additional hypothesis of the
theorem. The target and all imported declarations are unchanged.
The right-hand functor is the restriction of the constant sheaf formed
on the base site, exactly as in the target. This result makes no claim
about separately chosen sheafifications on the slice site, Harris
scheme models, adic completion, or cohomological comparison.

This is a derived internal proof of the existing Library proposition.
Its immediate provenance is the geometric theorem in
`TorsorSectionSplittingProof` (Worker 310) and the categorical
construction in `TrivializationFromSplitting` (Worker 149).
The original target's literature motivation is documented in
`TrivializationStatement.md`; the present composition does not claim
to follow an original-source proof. No new axioms or proof holes
are introduced.
