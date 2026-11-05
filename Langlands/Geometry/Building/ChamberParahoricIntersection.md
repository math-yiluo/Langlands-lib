# Intersections of actual chamber parahorics

The entry
`ParahoricBuildingData.chamberConjugateParahoricEquivCentralizerZeroImage_of_orderedRootInjectivity`
is the multiplicative equivalence

```text
(⋂ n : P.normalizerZeroComponent, P.parahoric (n • C))
  ≃* P.centralizerZero.map (rationalPoints.map P.centralizer.j).
```

The infimum is taken inside the actual rational-point group `G(F)`, and
`P.normalizerZeroComponent` is the existing subgroup `N(F) ∩ G(F)^0` with its
original apartment action. Both maps preserve the ambient rational point:
the construction is `MulEquiv.subgroupCongr` of a proved subgroup equality.
The accompanying application lemma states this explicitly.

The construction applies at arbitrary universe `u`, to every nonarchimedean
local field `F`, the existing actual `ParahoricBuildingData G`, and every
chamber `C`. Its explicit premises are:

- The apartment axioms `P.apartment.SatisfiesApartmentAxioms P.centralizer`.
- Actual rank-one factorization `RelativeRoot.HasRankOneFactorization P.i`.
- Local ordered-root injectivity `RelativeRoot.OrderedRootPointInjectivity P.i`.
- The full `P.ChamberIwahoriDecompositionStatement` for these actual data.

The last premise supplies sharp and full chamber products, their ranges, and
their ordered block versions under its existing apartment, chamber-point and
generic-cocharacter hypotheses. The intersection proof uses its full-product
and depth-zero ordered-block range conclusions. It does not prove that premise.

## Local ordered-root injectivity

`RelativeRoot.OrderedRootPointInjectivity i` is a proposition about one affine
group over one field and one torus embedding `i`. For every cocharacter `ν`,
every `n : ℕ`, and every injective `a : Fin n → characterLattice S` whose range
is exactly `indivisiblePositiveRoots i ν`, multiplication in that order is
injective on tuples of actual root-group rational points. Its factors are
exactly `(RelativeRoot.subgroup i (a r)).carrier (Over.mk (𝟙 _))`, and its
function is the product of their ambient rational points through `List.ofFn`.
It includes `n = 0`. It asserts no scheme isomorphism, product surjectivity,
or statement for other fields or embeddings.

The theorem
`RelativeRoot.orderedRootPointInjectivity_of_dynamicRootOrderedProduct`
obtains this local property from the published global
`DynamicRootOrderedProductStatement`, for a connected reductive group and its
actual maximal split torus. It specializes
`orderedRootSubgroupPoints_injective_of_statement` to the base test scheme.
The original global-Dynamic intersection declarations keep their names and
hypotheses as wrappers around the local versions. In particular,
`chamberConjugateParahoricEquivCentralizerZeroImage` and its application lemma
remain available with their previous interface.

## Implemented proof

The root-element lemma
`KPApartmentData.eq_one_of_forall_mem_filtration_affineWeylOrbit` is unchanged.
A nonidentity actual root element of nonnegative depth at every affine Weyl
translate of a chamber point has a finite root valuation. The valuation lemma
represents that valuation at every apartment point by an extended affine root
`psi`. Its value at the original chamber point is nonnegative and nonzero,
hence positive. AS 4 says that `psi` or `2 psi` is an actual affine root.
Reflection in that affine root belongs to the affine Weyl group and negates
the scaled value. The resulting negative value contradicts nonnegative depth
at the reflected point. Thus the root element is the identity.

The generalized ordered-block lemma
`eq_one_of_forall_mem_range_orderedChamberBlockProduct_of_orderedRootInjectivity`
fixes any injective enumeration of the indivisible roots positive on a
cocharacter. A point in every depth-zero block-product range has a tuple of
root coordinates at the original point and at every orbit point. Both tuples
map into the same actual unfiltered root groups. The local injectivity premise
identifies them. Each original coordinate therefore has nonnegative depth at
every orbit point, so the preceding reflection argument makes it the identity.
The original ordered product is the identity. This auxiliary lemma uses
neither connected reductivity nor maximality of the torus, and requires no
generic cocharacter or positive-rank hypothesis. Its surrounding apartment
data retain the monomorphic torus embedding and affine group assumptions.
The original global-Dynamic form follows from the specialization theorem above.

For the full parahorics, choose a generic integral cocharacter of the actual
maximal split torus and a point of `C`. The retained full decomposition writes
an element of the intersection as a negative unipotent factor, the actual
image of a centralizer-zero factor, and a positive unipotent factor. At every
affine Weyl translate of `C`, another such decomposition exists. The unchanged
private factor-comparison helper embeds both triples into the full ambient
Dynamic unipotent groups and `centralizerPoints P.i`. The published
`unipotentTripleProduct_injective` identifies their ambient negative and
positive factors. Each fixed factor therefore lies in its corresponding
ordered-block range at every orbit point. Local ordered-root injectivity and
the reflection argument remove both factors, leaving the actual
centralizer-zero image. That image lies in the generated full parahoric of
every subset, giving the reverse inclusion. This proves
`iInf_parahoric_affineWeylOrbit_eq_centralizerZeroImage_of_orderedRootInjectivity`
without the rank-one factorization premise.

To pass to the restricted normalizer, the unchanged
`exists_normalizerZeroComponent_lift_affineWeyl_of_rankOneFactorization` uses
the published apartment-reflection theorem to realize every affine Weyl
transformation by an actual normalizer point in the simply connected image.
The retained rank-one premise is used here. Containment of that image in
`P.zeroSubgroup` gives a point of `P.normalizerZeroComponent`. Equality of the
original affine actions identifies their images of `C`, so membership in
every restricted-normalizer translate implies membership in every affine
Weyl orbit chamber. The preceding argument proves
`iInf_parahoric_normalizerZeroComponent_eq_centralizerZeroImage_of_orderedRootInjectivity`
and the entry equivalence. The corresponding membership theorem
`mem_centralizerZero_of_forall_mem_parahoric_normalizerZeroComponent_of_orderedRootInjectivity`
uses the original normalizer points with explicit ambient zero-subgroup
membership, matching the existing saturation input's quantifiers.

## Provenance and remaining scope

This is an internal generalization of the published saturation proof by
Worker 1612 in this module. Worker 1315 identified that its ordered-product
use could be localized, and Worker 1672 implements that generalization.
The reflection, ambient three-factor comparison and actual normalizer-lifting
arguments are retained. The substantive change isolates their exact
rational-point injectivity requirement for the supplied embedding. All inputs
come from the current Library; no new external-source assertion is used.

The module retains the generated full parahorics, actual centralizer-zero
image, actual simply connected image and original apartment action. It does
not prove local root injectivity without its displayed premise or establish
the full chamber decomposition or rank-one existence. In particular this
intermediate unit does not prove the unchanged apartment-only
`ChamberConjugateIntersectionStatement` or `AffineIwahoriTitsStatement`.
Their remaining inputs must still be discharged independently.
