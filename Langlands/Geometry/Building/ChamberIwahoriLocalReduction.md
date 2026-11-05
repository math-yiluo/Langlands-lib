# Chamber decompositions and intersections from local algebraic inputs

This derived unit supplies the existing full chamber Iwahori decomposition
from three explicit algebraic inputs. It then applies the existing
chamber-intersection proof with that decomposition.

The entry
`ParahoricBuildingData.chamberConjugateParahoricEquivCentralizerZeroImage_of_rankOneFactorization`
is the ambient-point identity multiplicative equivalence

```text
(infimum over n : P.normalizerZeroComponent of P.parahoric (n • C))
  ≃* P.centralizerZero.map (rationalPoints.map P.centralizer.j).
```

It works in arbitrary universe `u`, for the existing actual
`P : ParahoricBuildingData G` over a nonarchimedean local field, with
the apartment axioms and a chamber `C`. Its three algebraic premises are:

- Actual rank-one factorization `RelativeRoot.HasRankOneFactorization P.i`.
- The actual cover comparison
  `P.zeroDatum.CoverImageCentralizerNormKernelStatement`.
- The global `RelativeRoot.DynamicRootOrderedProductStatement.{u}`.

The intersection uses the original action of the actual normalizer
restricted to the actual zero subgroup. Each parahoric is the existing
generated full parahoric, and the codomain is the image of the supplied
centralizer-zero subgroup.

## Implemented proof

`ValuationBuildingData.chamberSharpDecomposition_of_rankOneFactorization`
specializes the proof of
`chamberSharpDecomposition_of_prerequisites` to rank-one factorization
for the single supplied embedding `B.i`. The actual maximal split torus
is split. Smoothness of the actual connected reductive group gives local
finite type, and the split torus then gives finiteness of the relative
roots. The published relative-roots-and-restricted-characters spanning
theorem supplies the spanning condition.

For every generic cocharacter, the existing chamber exchange theorem
`KPApartmentData.sharpFixer_subset_mul_of_mem_chamber` uses those facts,
the retained local rank-one factorization and the apartment axioms to
give the sharp product inclusion. The existing
`chamberSharpConclusion_of_core` uses the retained Dynamic ordered-product
statement to obtain the sharp chamber conclusion.
`chamberSharpFacetConclusion_of_chamberSharpConclusion` supplies the
corresponding facet conclusion under the existing face and positive-system
conditions. Thus this step supplies the entire existing sharp decomposition
proposition, with its chamber membership and genericity conditions intact.

`ParahoricBuildingData.chamberIwahoriDecomposition_of_rankOneFactorization`
combines this sharp decomposition with
`centralizerParahoricIntersection_of_rankOneFactorization`. The latter
uses the same actual rank-one input and the retained actual cover
comparison to identify the centralizer intersection of each nonempty
generated full parahoric with the centralizer-zero image. The existing
`chamberIwahoriDecomposition_of_sharp` then proves
`P.ChamberIwahoriDecompositionStatement`, including its full chamber
and facet products.

Substituting this theorem into the existing restricted-normalizer
chamber-intersection equality proves
`iInf_parahoric_normalizerZeroComponent_eq_of_rankOneFactorization`.
The membership corollary has exactly the original normalizer and
zero-subgroup quantifiers of the corresponding conditional intersection
result. Finally the existing intersection equivalence, with this derived
decomposition, gives the entry. Its application lemma is reflexivity
because the equivalence preserves the ambient rational point.

## Provenance and scope

This is derived content from the current Library chamber-exchange,
sharp-decomposition, full-decomposition, point-parahoric centralizer
and chamber-intersection results. The first proof follows the published
`ChamberIwahoriPrerequisiteReduction` proof, retaining the factorization
input only at the embedding where it is used. No new external-source
assertion is introduced.

There is no separate boundedness or chamber-decomposition premise.
All three algebraic inputs remain assumptions; this unit proves none of
their universal versions. It does not prove the unchanged apartment-only
`AffineIwahoriTitsStatement` or the unconditional
`ChamberConjugateIntersectionStatement`.
