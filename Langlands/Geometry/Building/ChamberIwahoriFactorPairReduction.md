# Chamber decomposition and saturation from opposite factor pairs

The entry
`ParahoricBuildingData.chamberConjugateParahoricEquivCentralizerZeroImage_of_hasOppositeFactorPairs`
is the multiplicative equivalence

```text
(⋂ n : P.normalizerZeroComponent, P.parahoric (n • C))
  ≃* P.centralizerZero.map (rationalPoints.map P.centralizer.j).
```

It applies to the actual parahoric building datum over a nonarchimedean
local field in arbitrary universe `u`. The premises are the apartment
axioms, chamberhood of `C`, local `RelativeRoot.HasOppositeFactorPairs P.i`,
and `P.zeroDatum.CoverImageCentralizerNormKernelStatement`. Thus the only
additional algebraic inputs beyond the apartment and chamber hypotheses
are opposite-pair existence for this embedding and the actual cover
comparison. The entry is `MulEquiv.subgroupCongr` of the proved subgroup
equality. Both directions preserve the ambient rational point; the forward
coercion lemma is reflexivity.

Here `HasOppositeFactorPairs P.i` says that each nonidentity rational point
of each actual relative-root subgroup admits two opposite-root factors
whose product with that point normalizes the supplied torus. It assumes
neither uniqueness nor the further reflection and rank-one identities.
The cover comparison is the existing containment involving the actual
simply connected cover image and the centralizer norm kernel. Neither
premise is a replacement for the desired chamber-intersection conclusion.
The intersection uses the original action of `N(F) ∩ G(F)^0`; its target
is the image of the actual centralizer-zero subgroup in `G(F)`.

## Implemented proof

`RelativeRoot.orderedRootPointInjectivity_of_hasOppositeFactorPairs`
specializes the published all-test theorem
`orderedRootSubgroupPoints_injective_of_hasOppositeFactorPairs` at the
identity test scheme over the base field. The function is precisely the
existing ordered `List.ofFn` product of actual root-group rational points.
The resulting predicate quantifies over every cocharacter and every
injective finite enumeration of its indivisible positive roots, including
an empty enumeration. This bridge works for any smooth affine group over
any field, with a monomorphic split-torus map; it needs no maximal-split
or connected-reductive hypothesis.

For a valuation or parahoric building datum, its connected reductivity
provides smoothness and its maximal split torus provides splitness.
The published
`hasRankOneFactorization_of_hasOppositeFactorPairs` supplies the full
rank-one predicate from the same local pair-existence premise. The bridge
above supplies the local injectivity predicate.

`ValuationBuildingData.chamberSharpDecomposition_of_hasOppositeFactorPairs`
passes these two conclusions to the published local point-injectivity
reduction. This derives the full existing sharp chamber and facet
decomposition statement. Its apartment, chamber and genericity conditions
are quantified within that statement.
`ParahoricBuildingData.chamberIwahoriDecomposition_of_hasOppositeFactorPairs`
adds the explicit cover comparison and obtains the full existing chamber
and facet decomposition statement. Neither decomposition is assumed as a
separate premise.

The intersection equality applies the published local chamber-saturation
reduction with the derived rank-one and injectivity inputs and the supplied
cover comparison. The membership corollary puts an element in the subgroup
infimum by applying its hypothesis to each original normalizer point with
its explicit ambient zero-subgroup membership. Rewriting by the equality
gives the target membership. These are exactly the normalizer and
zero-component quantifiers of the published
`ChamberConjugateIntersectionStatement`.

## Provenance and remaining scope

This is an internal specialization and composition of published interfaces.
It combines the all-test local embedding of Worker 1302 and Worker 1315
with the local chamber reduction of Worker 1672 and its cited contributors.
The existing rank-one theorem supplies all consequences of a given
opposite pair. No new external-source assertion, root-group model, group
action or centralizer comparison is introduced.

Opposite-pair existence and the actual cover comparison remain explicit
premises. This module does not prove either from the apartment axioms.
Consequently it does not prove the unchanged apartment-only
`ChamberConjugateIntersectionStatement` or the unconditional
`AffineIwahoriTitsStatement`.
