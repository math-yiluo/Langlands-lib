# Extracting real ordinary tests from tensor evaluations

A continuous linear evaluation on a space with dense span of smooth pure
pairs is determined by its values on compact-finite pure pairs. The
Library's real smooth density theorem gives density in each smooth
standard factor. The product is dense, and continuity extends vanishing
on these pairs to all smooth pure pairs. The kernel of the linear
evaluation is closed, so it contains the whole space if it contains every
smooth pure pair. The same argument with the Schwartz row as a third
factor gives the equal-rank extraction.

`realOrdinarySmoothEvaluationExtraction` applies this reasoning to the
actual real ordinary test integrals, using the supplied opposite additive
scales and quotient measures. It takes a continuous pure map with dense
span and continuous normalized evaluations as hypotheses. At each
spectral point it assumes a tensor-space input with nonzero evaluation.
Agreement of the evaluations with the ordinary entire normalizations on
compact-finite pure inputs is also a hypothesis. The compact-finite
coefficient maps supply the vectors of the precise ordinary models.

For algebraic tensors, `finiteSum_of_algebraicPair` and
`finiteSum_of_algebraicTriple` expand a tensor whose normalized function
is one into finitely many pure tests. The equal-rank expansion enumerates
the finite sum in the last two factors for each summand in the first.

These are the density and finite expansion steps in H. Jacquet,
*Archimedean Rankin–Selberg Integrals* (2009), Theorems 2.3, 2.6 and
2.7, pp. 8–10, and §15, pp. 108–109 of the author-posted version.
