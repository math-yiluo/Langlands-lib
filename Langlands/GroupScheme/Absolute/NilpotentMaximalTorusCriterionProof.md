# Nilpotence criteria through maximal tori and Borel subgroups

`Langlands.GroupScheme.nilpotentMaximalTorusCriterion.{u}` proves the unchanged
[`NilpotentMaximalTorusCriterionStatement`](NilpotentMaximalTorusCriterionStatement.md).
Its type is exactly `NilpotentMaximalTorusCriterionStatement.{u}`. Over every
algebraically closed field, for every smooth connected affine group scheme,
it proves the equivalence of these four conditions:

1. every two maximal tori have equal all-test subgroup-functor ranges;
2. some Borel subgroup is geometrically nilpotent;
3. the ambient group is geometrically nilpotent;
4. every maximal torus is central on all scheme tests.

Nilpotence, maximality, the Borel condition and centrality have precisely
their meanings in the imported statement. No finite-type, characteristic,
dimension or nontriviality hypothesis is added. The statement and its
imported files are unmodified.

## Implemented proof

The helpers are in the namespace
`Langlands.GroupScheme.NilpotentMaximalTorusCriterion`.

`isCentral_of_borel_centralizes` proves a supporting assertion: if a Borel
centralizes a closed subgroup `j : H → G` on all tests, then `j` is central
in `G`. The published coefficient-orbit construction
`exists_affine_centralizer_orbit_of_projective` supplies an affine-valued
map from `G` with exactly the right centralizer cosets as fibers. Over the
base field the module-projectivity premise is automatic. The published
`IsBorelSubgroup.exists_properQuotient_of_solvableProperFixedPoint`,
with its remaining premise discharged by `solvableProperFixedPoint`,
supplies a smooth surjective quasi-compact projection `q : G → Q` onto
an actual proper Borel quotient. The Borel-centralizing assumption makes
the coefficient map constant on the fibers of `q`, so
`HomogeneousQuotientComparison.desc` descends it to `Q`.

The quotient is connected by surjectivity from `G`. Smoothness over the
field makes `G` reduced, and reducedness descends along the flat
surjection `q`. The theorem
`affineMap_eq_constant_of_proper_connected_reduced` makes the descended
map constant at the image of the identity. Its original all-test fiber
criterion then says every test point of `G` centralizes `j`, giving
`IsCentral j`. This argument applies to any closed subgroup `H` under the
stated centralizing assumption.

`nilpotent_of_nilpotent_borel` uses `borelMaximalTorus` to choose an
ambient maximal torus factoring through the specified nilpotent Borel.
`IsNilpotentGroupScheme.isCentral_of_isTorus` makes its map to the Borel
central. Transport along the Borel embedding gives the assumption of
the preceding helper, hence centrality in the ambient group.
`IsMaximalTorus.isNilpotentGroupScheme_of_isCentral_of_isAlgClosed`
from [`Nilpotent.EmptyRoots`](../Nilpotent/EmptyRoots.md) now yields
ambient nilpotence.

`central_of_unique_maximal_tori` first uses uniqueness to identify the
range of a maximal torus with each of its rational conjugates.
Representability of its closed normalizer and
`SubgroupFunctor.range_le_of_algClosed_points` promote this rational-point
containment to all-test containment in the normalizer. The original
torus range is therefore normal. The published finite-Galois splitting
theorem makes the torus split over the algebraically closed base, and
`isCentral_of_isNormal_of_isSplitTorus` makes it central.

`range_eq_of_central_maximal_tori` applies `maximalTorusConjugacy`.
Centrality makes the conjugation of the first torus inclusion equal to
itself on every test. The resulting isomorphism of the two torus
inclusions gives equality of their subgroup-functor ranges.

`borel_id_of_solvable` checks the Borel predicate for the identity
embedding of a smooth connected solvable group. Any closed overgroup
through which the identity factors is an isomorphism, by monicity of its
closed embedding.

The final `List.TFAE` proof assembles uniqueness ⇒ centrality,
centrality ⇒ nilpotence using existence of a maximal torus,
nilpotence ⇒ centrality, centrality ⇒ uniqueness,
a nilpotent Borel ⇒ nilpotence, and nilpotence ⇒ a nilpotent Borel.
The last implication uses solvability of a nilpotent group and its
identity Borel. The published torus-descent theorem supplies nilpotence
⇒ centrality.

## Provenance

This is an internal deduction from the imported Library theorems.
The unchanged statement records the original source and its conventions:
James S. Milne, *Algebraic Groups* (2017), Proposition 17.23, printed
p.359, source ID `milne-2017-algebraic-groups`. Its paired Markdown
records the algebraically closed, affine, connected group-variety scope
and the comparison of the Library's predicates with Milne's.

The implemented proof uses a proper Borel quotient and an affine
coefficient orbit for the Borel implication, replacing Milne's dimension
induction. It derives uniqueness ⇒ centrality directly through the
normalizer. It uses the published maximal-torus conjugacy and
nilpotent-torus centrality results, and does not assume
`BorelCentralizerCenterStatement`.
