# Rational rank-one length two from special-vertex compact inputs

Worker 3915, Task 3915 (`c53e3363-ffa5-4f01-ae77-aca8e1f49117`).

This internal composition derives the unchanged
`Langlands.Aubert.General.RationalPointFamily.RationalRankOneLengthTwoStatement.{u, v}`
from special-vertex compact inputs. It does **not** prove that unconditional
target: its one additional hypothesis remains explicit and unproved. The
target and all imported Lean/Markdown pairs are preserved.

## Declarations and scope

In namespace `Langlands.Aubert.General.RationalPointFamily`,
`rationalRankOneLengthTwo_of_specialVertexInputs` has exactly one outer
hypothesis,
`Langlands.CuspidalSupport.RationalSpecialVertexCompactInputsStatement.{u}`,
and concludes the entire unapplied length-two proposition at universes `u, v`.
The field and representation universes remain independent. The target retains
every nonarchimedean local field, connected reductive group scheme, actual
maximal split torus, generic cocharacter, topology, root labels, restricted
Levi decomposition, and displayed premise. Carriers remain in
`Type (max (u + 1) v)`. No finite-length-preservation, admissibility, splitting,
semisimplicity, or new K0 assumption is introduced.

`rationalRankOneLengthTwo_of_jointBasis` gives the same conclusion from
`Langlands.BruhatTits.SpecialCompact.JointSpecialCompactBasisExistenceStatement.{u}`.
It uses the published adapter that extracts the four compact-input clauses
from one common geometric witness of that stronger statement.

The entry definition `rationalRankOneLengthTwoOfSpecialVertexInputs` has the
Prop-valued type
`RationalSpecialVertexCompactInputsStatement.{u} →
RationalRankOneLengthTwoStatement.{u, v}`. Its value is the first theorem.
It records a conditional reduction, following the existing internal
`rationalRankOneLengthTwoOfExtraction` definition.

## Implemented argument

The proof is composition of published declarations:

1. `rationalCuspidalJacquetFactorExtraction_of_specialVertexInputs`
   ([RationalCuspidalExtractionFromSpecialVertex](RationalCuspidalExtractionFromSpecialVertex.md))
   derives actual cuspidal Jacquet-factor extraction from the compact inputs.
2. `rationalRankOneLengthTwo_of_extraction`
   ([RationalRankOneLengthTwoReduction](RationalRankOneLengthTwoReduction.md))
   combines extraction-based maximal Jacquet detection with the unconditional
   `rationalMaximalCuspidalJacquetBudget`. Exactness of the finite family of
   maximal Jacquet functors bounds the induction's actual composition length
   by two. Nonzeroness and reducibility yield two irreducible factors and an
   actual short exact sequence in either factor order.
3. For the second theorem,
   `Langlands.CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis`
   supplies the first theorem's hypothesis. Its finite Cartan cover is proved
   at the very same special compact subgroup using `rationalPositiveCartanCover`.

The empty simple-root type is retained; there is then no maximal label, and
the length-two conclusion is vacuous. The composition unfolds no target
definition and changes no quantifier.

## Declaration-level dependencies

A private Lean diagnostic traversed the types and values of every constant
reachable from the entry definition and, separately, from
`rationalRankOneLengthTwo_of_jointBasis`. Opaque theorem values were included,
as were the constructors of reachable inductive declarations. Every visited
constant resolved in the environment. This is a declaration dependency
inspection, not independent semantic review or an unconditional proof.

In the following table, `RP` abbreviates
`Langlands.Aubert.General.RationalPointFamily` and `AG` abbreviates
`Langlands.Aubert.General`. All named declarations occur in the inspected
closure. Their paired Markdown describes the underlying arguments.

| Ingredient | Actual declarations and scope |
| --- | --- |
| Length bound | `RP.rationalRankOneLengthTwoFromInputs` uses `AG.repLength_le_two_of_jacquetFamily`, `Langlands.exactFamilyLengthBound`, and `AG.jacquetFunctor_map_isShortExact`. These give finite length from detection by the finite family of actual maximal normalized Jacquet functors and its total length budget; finite length of induction is not assumed. `RP.rationalStandardInductionNonzero` and `AG.exists_hasTwoConstituents_of_length_le_two` then give the actual two-factor short exact sequence. |
| Cuspidal Jacquet detection | `RP.rationalMaximalCuspidalJacquetDetectionFromExtraction` uses `RP.exists_irreducible_cuspidal_jacquet_subquotient`. The latter supplies an actual nonzero standard Jacquet module and an irreducible cuspidal subquotient in it, without finite length of the ambient representation. This minimal-Jacquet existence result is a transitive cuspidal-support ingredient of the composition. Extraction and actual root association make its index maximal. |
| Geometric lemma for the budget | `RP.rationalMaximalCuspidalJacquetBudget` uses `RP.rationalMaximalSourceGeometricFiltration`, `RP.pointGeometricObjectFiltrationOfEpsilonBalance`, and `RP.jacquetSupportGeometricTermIso`. These are the actual rational-point object filtration and its normalized grades. `RP.pointCoatomJacquetBudget_of_geometricFiltrations` bounds the total coatom length by two for an irreducible cuspidal inducing object. |
| Geometric lemma for extraction | `RP.rationalCuspidalJacquetFactorExtraction_of_specialVertexInputs` passes through `RP.rationalCuspidalExtractionInputs_of_specialVertexInputs`, `RP.exists_pointInducedJacquetGeometricFiltration`, `RP.rationalCuspidalJacquetFactorExtraction_of_inputs`, and `RP.pointCuspidalJacquetFactor_of_geometricFiltration`. These extract the actual root-associated factor from the filtration of an inside-Levi Jacquet module of normalized induction. |
| First adjointness | `AG.hom_eq_zero_of_isCuspidalFor_of_induction` uses `AG.FirstAdjointness.equiv` for the actual normalized induction and Jacquet functors with unimodular radical. The cuspidal source has zero proper Jacquet module, so every such map into proper induction is zero. This is applied inside each actual standard Levi by `RP.pointLeviStandardInductionCuspidalExclusion_of_specialVertexInputs`. |
| Compact restriction and projectivity | `AG.rationalCuspidalCompactRestriction` supplies compact smooth-dual coefficients on the actual norm kernel from the special-vertex compact data. `RP.rationalCompactRestrictionCuspidal` proves the converse. `AG.compactRestrictionSubrepresentation_ne_bot_of_isSubquotient` uses `Langlands.CompactCoefficient.allProjectiveLift` to lift the restriction of a nonzero compact-coefficient subquotient; `AG.not_isSubquotient_of_compactRestriction` combines this with first adjointness to prove proper-induction exclusion. These are the published alternate VI.5.2 argument, without the whole-category splitting. |
| Actual Weyl and Levi comparisons | `RP.rationalWeylComparison` supplies the rational-point normalizer and centralizer comparisons. `RP.rationalLeviCuspidalityTransport` identifies intrinsic cuspidality on the represented standard Levi scheme with the target's restricted-subgroup predicate. These retain the actual maximal split torus, root labels and canonical topology. |
| Joint-basis adapter | The second theorem additionally uses `Langlands.CuspidalSupport.rationalSpecialVertexCompactInputs_of_jointBasis`, including `RP.rationalPositiveCartanCover`, to provide the compact-input witness at the same special vertex. |

No Langlands-classification proof, independence theorem for representation
characters, second adjointness, Renard VI.3.5 whole-category splitting, or
fixed-level cuspidal finiteness is reached in either declaration closure.
The closure does reach the module
`Langlands.Representation.Classification.SupercuspidalSupport`, but only its
generic `Langlands.SmoothRep.hom_hom_injective`,
`Langlands.SmoothRep.hom_hom_surjective`,
`Langlands.SmoothRep.isSubquotient_iff_exists`, and
`Langlands.SmoothRep.IsSubquotient.of_iso_right`, together with generated
helpers. These statements work for arbitrary smooth representations of a
topological group; no GL support-existence or classification assertion from
that module is used. The checked axioms of the entry definition are
`propext`, `Classical.choice`, and `Quot.sound`.

## Provenance and remaining prerequisite

This is an internal derived composition of the published implications named
above. It makes no new claim of original-source verification. Their paired
Markdown records the source correspondence to the length-two step of
Aubert's Corollary 1.10(b), Casselman section 7.1, and Renard's geometric lemma
and proper-induction exclusion.

The special-vertex compact inputs remain unproved. Task 4169
(`8c39faa0-2a70-4fc4-a027-914987aba924`) owns the stronger joint existence
target. Task 4358 (`e6add7c5-44c5-45ea-afe9-7f48c98fb927`) owns unconditional
cuspidal Jacquet-factor extraction, which also suffices directly through the
existing reduction. Neither task's assignment nor its draft is proof evidence.
The whole-category cuspidal splitting of Renard VI.3.5 and fixed-level
cuspidal finiteness are not additional hypotheses of this route. Completion
of Task 3915 still requires an unconditional proof of its exact target,
independent semantic review, and publication.
