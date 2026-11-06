# Special points as vertices of the actual valuation building

This internal construction regards a supplied special point of the existing
valuation-building quotient as a special vertex of that same quotient.
It requires the supplied apartment roots to satisfy
`AffineRootSystem.IsAffineRootSystemWithRankZero`. It applies in every field
universe, including rank zero, without an apartment-injectivity, opposite-pair,
or topology-compatibility premise.

For an affine space with a rank-zero-compatible affine root system, the theorem
`AffineRootSystem.isVertex_of_isSpecialPoint` proves that the facet of a special
point `x` is `{x}`. Every point `y` in that facet belongs to the hyperplane of
every root vanishing at `x`, by the published `facet_subset_hyperplane`.
The published `eq_of_isSpecialPoint_of_vanishingRoots` then gives `y = x`.
Conversely, `x` belongs to its own facet. These are exactly the two inclusions
in the implemented proof of the singleton equality.

The building theorem `ValuationBuildingData.isVertex_of_isSpecialPoint` unpacks
specialness as a rational-point translate of an apartment special point.
Applying the affine theorem to that point supplies the vertex witness with
the same translating group element. Thus the result uses the existing
`ValuationBuildingData.IsSpecialPoint` and `IsVertex` predicates on the original
`ReducedBuilding`, with its original rational-point action.

`ValuationBuildingData.specialVertex` returns the subtype of points satisfying
both predicates. Its underlying point is the supplied `y` by definition,
as recorded by `coe_specialVertex`. It makes no new choice of a point and
preserves every point stabilizer.

The provenance is internal: the proof composes the separation theorem in
`SpecialPointFixedLocus` with facet membership and the existing translated
definitions in `ValuationBuildingData` and `KPBuilding`. It introduces no
external source assertion.

This unit does not construct valuation-building data or a special point.
It supplies the vertex consequence once those data and that point are given.
The metric, building axioms, apartment injection, global fixed-point
uniqueness, supplied-model identification, and the unconditional
`IntegralModel.BuildingComparisonStatement` remain separate obligations.
