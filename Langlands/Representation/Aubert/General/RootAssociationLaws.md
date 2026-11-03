# Elementary laws for actual root association

Worker 64. This internal construction uses the literal simple-root labels and
the actual normalizer action of
[`RationalStandardComplex`](RationalStandardComplex.md). It adds no root-system,
Coxeter, topology, admissibility or representation-theoretic premise.

`rootAssociationEquiv` constructs an equivalence between the finite types of
labels in `I` and `J` from `rootAssociation i ν hN hZ I J n`. The field, group
scheme and torus are those of the published association definition. The
affineness and monomorphism instances and both point-subgroup comparison inputs
remain explicit. No connectedness or reductivity hypothesis is needed for these
elementary deductions.

The construction first identifies each label subset with its image `rootSet`
under the injective map taking a simple-root label to its actual character.
The supplied association witness gives an actual normalizer representative.
Its Weyl action is an invertible integral linear map on the character lattice.
Restricting this map to `rootSet I` gives an equivalence with its image, and the
association's image equality identifies that image with `rootSet J`. Composing
these equivalences gives the result. The construction uses classical choice for
the supplied witness and the inverse of the restricted injective map.

`rootAssociation_one` proves reflexivity with the literal identity
representative: the quotient homomorphism and character-action homomorphism both
take the identity to the identity.

`rootAssociation_card_eq` applies `Fintype.card_congr` to the constructed
equivalence. This requires no finite instance on the entire simple-root type,
since the two individual subsets are finite. `rootAssociation_empty_iff` follows
by the zero-cardinality criterion. When the whole simple-root type is finite,
`rootAssociation_univ_iff` uses `Finset.card_eq_iff_eq_univ` to show that one
subset is full exactly when the other is. `rootAssociation_ne_univ` records the
resulting preservation of properness. Empty simple-root types are allowed.

These are deductions from the existing definitions, with no external source
claim. The actual dependencies are `rootAssociation`, `rootSet` and
`weylCharacterAction`, the generic restricted-image equivalence
`Equiv.Set.image`, and finite-cardinality identities. The module proves neither
Levi conjugation nor a geometric lemma, Jacquet nonvanishing, support detection,
or the full `RationalRankOneJacquetModulesStatement`.
