# The surjective-commutator branch of Borel self-normalization

This internal contribution combines existing character, Chevalley stabilizer,
homogeneous orbit and quotient constructions. It does not prove
`BorelNormalizerStatement`. In particular, the required rational factorization,
surjective commutator and proper homogeneous quotient remain explicit inputs.

For any base scheme, `SubgroupFunctor.normalizerFactor` factors a subgroup
homomorphism through any representative of its all-test normalizer.
`normalizerFactor_comp` proves compatibility with the inclusion. The construction
uses the existing factorization through a represented subgroup and the fact that
every subgroup normalizes itself.

Over an algebraically closed field of arbitrary universe, the main normality
lemma considers a connected reduced affine group locally of finite type and a
closed subgroup whose source is reduced and locally of finite type. Suppose
morphisms from a unipotent group and a reduced group locally of finite type
multiply surjectively onto the subgroup's rational points. Suppose a base point
of the all-test normalizer has commutator on the second factor equal, on rational
points, to a scheme-surjective endomorphism locally of finite type of that
factor. Finally, supply a flat surjective quasi-compact morphism from the ambient
group to a proper relative scheme. Equal quotient images must imply that the
right difference belongs to the subgroup on every scheme test.

The proof takes a closed representative of the all-test normalizer and applies
the actual Chevalley line-stabilizer theorem to it. The original subgroup factors
through this representative, and the normalizing rational point lifts to it.
Monicity transfers the commutator identity. The coordinate-line fixed-vector
theorem then makes the defining coordinate vector fixed by the original
subgroup: its line character vanishes on the unipotent factor and on the
surjective commutator factor, and rational factorization detects its triviality.
The homogeneous orbit theorem makes that vector fixed by the connected reduced
ambient group, using the supplied proper quotient. Exactness of the line
stabilizer forces the normalizer to equal the whole group on every scheme test.
Its normalization property therefore proves normality of the original subgroup.
No smoothness or reducedness of the normalizer is required.

The final Borel corollary starts with a smooth connected affine ambient group
and the existing Borel predicate. It accepts abstract normalizer membership in
the rational point group, converting it to all-test normalizer membership with
`normalizer_range_carrier_base_eq_algClosed_points`. Smoothness supplies the
needed reducedness and local finite type. The normality lemma and
`isIso_of_normal_of_proper_homogeneousQuotient` prove that the Borel inclusion is
an isomorphism. This last step explicitly retains
`NormalSubgroupQuotientStatement`, as well as the actual proper homogeneous
quotient and the rational factorization and commutator inputs.

The provenance is internal: this is a composition of the imported implemented
results. It supplies the surjective-commutator implication needed by the host
proof, without asserting the existence of those structural inputs or handling
the separate central-kernel branch.
