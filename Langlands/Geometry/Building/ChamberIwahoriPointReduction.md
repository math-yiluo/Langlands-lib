# Chamber decomposition and saturation from local root injectivity

The entry
`ParahoricBuildingData.chamberConjugateParahoricEquivCentralizerZeroImage_of_localRootInjectivity`
is the ambient-point identity multiplicative equivalence

```text
(⋂ n : P.normalizerZeroComponent, P.parahoric (n • C))
  ≃* P.centralizerZero.map (rationalPoints.map P.centralizer.j).
```

It applies at arbitrary universe `u` to the actual parahoric building datum
over a nonarchimedean local field and a chamber `C`. Its hypotheses are the
apartment axioms, `RelativeRoot.HasRankOneFactorization P.i`, the actual
`P.zeroDatum.CoverImageCentralizerNormKernelStatement`, and
`RelativeRoot.OrderedRootPointInjectivity P.i`. The last predicate asserts
injectivity of the actual positive-root ordered multiplication on rational
points for this supplied torus embedding, every cocharacter, and every
injective enumeration of the indivisible positive roots. The module derives
the full chamber decomposition from these local inputs; it does not retain
the chamber decomposition as a separate premise.

The equivalence uses `MulEquiv.subgroupCongr` of the proved subgroup equality.
Both directions therefore preserve the underlying point of `G(F)`; the
application lemma is reflexivity. The subgroup infimum is taken inside the
actual rational-point group and uses the original action of the actual
restricted normalizer `N(F) ∩ G(F)^0`. The central factor is the image of the
actual `P.centralizerZero` under its representing inclusion.

## Implemented reduction

`KPApartmentData.orderedChamberBlockInjectivity_of_orderedRootPointInjectivity`
restricts root-point injectivity to the existing chamber block maps, for
both Boolean depths and every apartment point. Each root in an enumeration
belongs to the actual root set, and the published chamber-block containment
embeds its block into the corresponding unfiltered root group. Two tuples
with equal block products then have equal lifted root-group tuples by the
local injectivity premise. Equality of their ambient coordinates gives the
original tuple equality. The maps, factor order and doubled-root blocks
are unchanged; the proof includes an empty enumeration.

`ValuationBuildingData.chamberSharpDecomposition_of_localRootInjectivity`
uses connected reductivity and the actual maximal split torus already in the
valuation datum to obtain finiteness of the root set and spanning by
restricted characters. The retained actual rank-one input then supplies
the right-central sharp-fixer core inclusion at each chamber point, via
`sharpFixer_subset_mul_of_mem_chamber`. Apartment axioms supply the extended
affine-root-system laws, derivative comparison and AS4. The preceding
restriction gives local block injectivity. The generalized
`chamberSharpConclusion_of_core_of_blockInjectivity` combines these inputs
to prove every clause of the existing sharp chamber conclusion. The
published facet-transport theorem gives the entire sharp facet conclusion
under the existing face and geometric positive-system hypotheses. Thus the
result is the unchanged full `ChamberSharpDecompositionStatement`.

`ParahoricBuildingData.chamberIwahoriDecomposition_of_localRootInjectivity`
applies the existing reduction from sharp to full chamber decompositions.
The actual rank-one and cover/centralizer comparison premises provide the
centralizer-parahoric intersection through
`centralizerParahoricIntersection_of_rankOneFactorization`. The sharp result
above supplies its other input. All full chamber and facet conclusions are
therefore obtained without a global ordered-product proposition.

The subgroup equality and membership lemmas then apply the generalized
local-injectivity saturation argument in `ChamberParahoricIntersection`,
using this derived full decomposition. That argument fixes the unipotent
coordinates across the affine Weyl orbit, eliminates each root coordinate
by its own affine-root reflection, and lifts each Weyl transformation to the
actual zero-component normalizer under the retained rank-one premise. The
reverse inclusion is centralizer-zero containment in every full parahoric.
The membership lemma
`mem_centralizerZero_of_forall_mem_parahoric_of_localRootInjectivity`
quantifies over original normalizer points with explicit ambient
zero-subgroup membership, matching the existing saturation target.

## Provenance and scope

This is an internal specialization and assembly of the existing chamber,
sharp-fixer, centralizer-comparison and affine-Weyl saturation interfaces.
Worker 1672 implements the local restriction and assembly. The sharp-core
argument of Workers 1267 and 1536, the local chamber and saturation route of
Worker 1612, and Worker 1315's identification of the local injectivity
requirement supply its reused mathematical content. No new external-source
assertion, group model, root group or apartment action is introduced.

Actual rank-one factorization, the actual cover/centralizer comparison and
local root-point injectivity remain displayed hypotheses. This module does
not discharge them from the apartment axioms. It proves neither the exact
apartment-only `ChamberConjugateIntersectionStatement` nor the unconditional
`AffineIwahoriTitsStatement`; those closing obligations remain separate.
