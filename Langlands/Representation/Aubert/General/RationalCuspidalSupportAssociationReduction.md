# Actual rational support association reduced to cuspidal factor extraction

Authors: Worker 55.

`rationalCuspidalSupportAssociation_of_cuspidalJacquetFactorExtraction` proves
the implication from the exact named
`RationalCuspidalJacquetFactorExtractionStatement.{u, v}` to the exact named
`RationalCuspidalSupportAssociationStatement.{u, v}`. This is a conditional
internal reduction. The extraction proposition is a hypothesis, and this pair
does not prove it or claim a closed proof of support association.

The proof introduces the original support statement's rational-point data,
canonical evaluation topology and displayed hypotheses. It applies the generic
common-factor reduction from `CuspidalJacquetFactorAssociationReduction`.
The required inversion and product laws are the published
`rootAssociation_inv` and `rootAssociation_mul`.

For an irreducible ambient representation `π`, its irreducibility supplies
nontriviality of its actual carrier. The imported
`exists_irreducible_cuspidal_jacquet_subquotient` then gives one standard index
`J` and an actual irreducible cuspidal subquotient `τ` of `r_J(π)`. The generic
reduction applies the assumed extraction proposition to each of the two given
induction occurrences, using this same `τ`. It composes their actual
isomorphisms with the representative `n₂⁻¹ * n₁`, which also supplies the root
and actual Levi comparisons. Nonvanishing of the chosen Jacquet module,
additionally supplied by the factor-existence theorem, is not needed here.

The universes `u` and `v` remain independent, and the smooth carriers have
the original universe `max (u + 1) v`. The exact original structural and
topological scope is retained. No induction realization of `τ`, finite-length
condition, admissibility condition or extra compactness hypothesis is added
to the support-association proposition.

The provenance is internal. This proof specializes published algebraic
composition and factor-existence results and applies extraction as a
hypothesis. Its remaining mathematical prerequisite is a closed proof of that
exact extraction statement.

The factor-existence proof has the following declaration-level dependencies.
`exists_nontrivial_isLeviCuspidal_jacquet` chooses a standard index of minimal
cardinality with nonzero Jacquet module. Its vanishing-in-stages argument uses
`CuspidalEmbedding.mem_relations_of_subsingleton`,
`CuspidalEmbedding.subsingleton_jacquet_of_forall_mem_relations`, and
`CuspidalEmbedding.closedNormalizerCharacter_eq_one_of_compactLimit`.
Although these helpers are in `RationalCuspidalEmbeddingProof`, the proof does
not apply its stronger `rationalCuspidalEmbedding` theorem or first adjointness.
`SmoothRep.exists_isIrreducible_isSubquotient_of_nontrivial` then takes an
irreducible quotient of a nonzero cyclic subrepresentation. Its generic
maximal-subrepresentation steps are
`CuspidalSupport.QuasicuspidalEmbedding.exists_isCoatom_subrepresentation` and
`CuspidalSupport.QuasicuspidalEmbedding.isIrreducible_of_isCoatom`; they apply
to arbitrary group representations and impose no reductive or GL condition.

Cuspidality passes to this actual subquotient through
`IsLeviCuspidal.of_isSubquotient` and
`jacquet_subsingleton_of_isSubquotient`. The latter applies
`jacquetFunctor_map_isShortExact`, whose proof uses the published
`Jacquet.Localization.characterLocalizationExactness` for all smooth short
exact sequences with compact-limit unipotent subgroup. For each inner test,
that hypothesis is supplied by
`standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement`
and `isLimitOfCompactSubgroups_subgroupOf`, using the original `hStandard` and
closedness of the chosen Levi. Exactness and compact-limit are thus proved
inputs at these calls, rather than added premises of support association.

No classification, character-independence, geometric-lemma or adjointness
theorem is applied in this conditional assembly or in the factor-existence
steps just described. The extraction proposition is still a premise; this
dependency account does not supply or anticipate the dependencies of its
future closed proof.
