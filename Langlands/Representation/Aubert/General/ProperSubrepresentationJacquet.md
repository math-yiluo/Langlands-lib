# Jacquet modules of proper subrepresentations of actual induction

This internal deduction uses the published actual normalized induction and
Jacquet functors for subgroup semidirect decompositions of a locally compact
nonarchimedean group. The group and inducing carrier universes are independent;
induction and its subrepresentations have carriers in `max uG uV`.

`subrepresentationJacquetInclusionEquiv` assumes that the actual Jacquet module
of induction along the inducing parabolic is irreducible. For every nonzero
invariant subspace, it constructs an actual representation equivalence from
the Jacquet module of the subspace onto that of the induction. Its underlying
map is exactly Jacquet restriction of the original inclusion. Compact-limit
exactness makes this map injective. Actual normalized first adjointness makes
its source nonzero, and irreducibility of its target makes it surjective.
Compact-limit unimodularity supplies the modulus input of first adjointness.
No finite-length assumption or inducing irreducibility is used.

`quotient_jacquet_subsingleton_of_irreducible_induction_jacquet` then proves that
the quotient by the nonzero subspace has zero Jacquet module along the inducing
parabolic. The proof uses the actual short exact sequence and the surjectivity
of the constructed inclusion map.

`proper_subrepresentation_second_jacquet_subsingleton` additionally assumes
that a second actual Jacquet module of the induction is irreducible, and that
these two Jacquet modules detect zero for the displayed quotient. It proves
that the second Jacquet module of any nonzero proper subrepresentation is
zero. The proper quotient is nonzero, so its second Jacquet module cannot
vanish after the first has vanished. The resulting nonzero quotient map out
of the second simple middle Jacquet module is injective. Exactness forces its
first endpoint to be zero. The second parabolic can have a different Levi;
no relation between the two subgroups is presumed.

This is a derived algebraic step for the nonself-associated rank-one
argument. It introduces no external source assertion. The simplicity of the
two middle Jacquet modules, the displayed two-module detection statement,
their realization for the actual rational-point group, the remaining Jacquet
support bounds, the exponent sign argument, square integrability and unitarity
are separate obligations. In particular this pair supplies no geometric
lemma, cuspidal-support detection theorem or proof of the exact
`RationalRankOneSelfAssociationStatement`.

The declaration-level dependencies are
`FirstAdjointness.nontrivial_jacquet_of_map_ne_zero`,
`isUnimodularModulus_of_isLimitOfCompactSubgroups`,
`subtype_mkQ_isShortExact`, `jacquetFunctor_map_isShortExact`, and Mathlib's
`Representation.IsIrreducible.surjective_or_eq_zero` and
`Representation.IsIrreducible.injective_or_eq_zero`. The first-adjointness
map is the published actual descended evaluation map, constructed in
`General.FirstAdjointness.equiv`; no adjointness assertion is supplied as a
hypothesis here. Jacquet exactness is the published compact-limit quotient
exactness result. This deduction uses no classification, character
independence, geometric-lemma or cuspidal-support theorem. In particular it
does not invoke the conditional support-category detection implication in
`SupportCategoryReductions`; it imports that module for the elementary
`subtype_mkQ_isShortExact` lemma only.
