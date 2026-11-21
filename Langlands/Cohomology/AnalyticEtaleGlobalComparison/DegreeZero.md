# Degree-zero comparison on compact analytic étale sites

`Langlands.Cohomology.AnalyticEtaleGlobalComparison.isIso_etaleGlobalInclusion_of_compactSpace`
proves invertibility of the canonical inclusion of smooth global sections for
compact Hausdorff `X`. The proof uses étale openness and ordinary-point joint
surjectivity of covering sieves to obtain finite subcovers at the twisted
base. The finite descent theorem then shows that every ordinary global
section of a restricted étale `G`-sheaf is smooth.

`isIso_etaleComparison_zero_of_compactSpace` applies this result to the
canonical degree-zero cohomology comparison. The private base-change lemma
checks the three factors of that map. Exactness makes the postcomposition
comparison invertible. The right-derived inverse of the global-section
inclusion inverts its right-derived map. The Library's degree-zero
composite comparison is invertible by left exactness of restriction and
ordinary global sections.

`etaleComparisonZeroIsoOfCompactSpace` packages the result as a natural
isomorphism. Its forward transformation is `etaleComparison ρ R 0` by
`etaleComparisonZeroIsoOfCompactSpace_hom`.

The two theorems specialize published finite-cover descent and derived
base-change constructions to the degree-zero part of the Library's
analytic étale global comparison. The second theorem uses the target's
smallness and admissible-refinement instances. The higher-degree comparison
requires the separate acyclicity argument for restricted injectives.
