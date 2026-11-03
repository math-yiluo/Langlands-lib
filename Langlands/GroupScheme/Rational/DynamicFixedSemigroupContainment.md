# Factorization through nonnegative and zero Dynamic representatives

This internal construction supplies morphisms from smooth connected closed
invariant subgroups to the actual affine Dynamic parabolic and centralizer
representatives. It also proves the all-test subgroup inclusions that induce
those morphisms. It applies to every field and universe, every split torus,
every homomorphism from it, and every cocharacter, including zero and nongeneric
cocharacters. The ambient group needs only affineness and local finite type;
its smoothness and connectedness are not assumed.

Let `F` be a smooth connected closed subgroup functor of `G`, stable under
conjugation by the entire split torus `S`, and let `nu` be a cocharacter of `S`.
If the actual tangent submodule of `F` lies in the torus weight span whose
pairing with `nu` is nonnegative, then `F` lies in
`Dynamic.parabolic (groupHom nu ≫ i)`. If that tangent submodule lies in the
zero pairing span, then `F` lies in the corresponding `Dynamic.centralizer`.
The containment is in `SubgroupFunctor`, hence holds on every test scheme.

The data constructions `dynamicParabolicFactorOfTangent` and
`dynamicCentralizerFactorOfTangent` take any representative `j : H → G` of
`F` and return a morphism to the existing affine Dynamic representative. Their
`_comp` theorems say that composing with its ambient inclusion recovers `j`.
The general represented-subgroup `homOfLe` construction supplies these lifts
from the proved inclusions.

The containment proofs select the smooth connected closed representative of
`F`, induce the original torus action on it, and restrict along `nu`. The
representative is affine because its inclusion in affine `G` is closed. Its
inclusion intertwines the induced action with conjugation by `groupHom nu ≫ i`.
Closed equivariant reflection identifies the original action parabolic or
centralizer with the inverse image of the ambient Dynamic functor.

Each Lie point of the representative maps into the tangent submodule of `F`.
The tangent bound, the published cocharacter weight-span conversion, and
`dynamicLie` put its image in the ambient Dynamic functor. The reflection
identity therefore puts every Lie point in the induced action functor.
`AutomorphicAction.parabolic_eq_top_of_lieKernel` or its centralizer analogue
then proves that functor is the whole representative. Applying reflection on
an arbitrary test gives the claimed inclusion of `F`.

The auxiliary module `Dynamic.ActionLieContainment` proves these full-Lie
criteria through the actual semidirect group scheme. Its proof and precise
hypotheses are described in that module's paired Markdown. Neither criterion
assumes a semigroup realization, a uniqueness theorem for a generated subgroup,
or the desired Dynamic-semigroup comparison.

Finally, `nonnegative_generator_le_dynamicParabolic` and
`zero_generator_le_dynamicCentralizer` convert the intrinsic support bound of
each admissible semigroup generator to its tangent bound using the published
split-torus support theorem, and apply the containment results. These are the
reverse-inclusion ingredients for the host's three-part comparison. This unit
does not yet assert the lower inclusions or the full comparison.

The provenance is internal: the constructions combine the published represented
action, closed equivariant reflection, actual Dynamic smoothness and Lie image,
cocharacter weight-span and intrinsic support adapters, and smooth full-Lie
closed-subgroup equality. No new literature translation is asserted.
